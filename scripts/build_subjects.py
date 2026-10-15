"""Build every local module through Lake with bounded compiler concurrency.

Build logs and resumable state live in tmp/organization-build.
A final ordinary Lake build checks the complete library and its cache traces.
"""

from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
from pathlib import Path
import argparse
import hashlib
import json
import os
from queue import Empty, SimpleQueue
import re
import shutil
import subprocess
import sys
import time

from check_module_layout import ROOT, inventory, order


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument("--batch-size", type=int, default=1,
                        help="Ready modules per Lake invocation; each worker compiles them sequentially.")
    parser.add_argument("--resume", action="store_true")
    args = parser.parse_args()
    if args.workers < 1:
        parser.error("--workers must be positive")
    if args.batch_size < 1:
        parser.error("--batch-size must be positive")
    files, deps = inventory()
    sequence = order(deps)
    hashes = {name: hashlib.sha256(path.read_bytes()).hexdigest() for name, path in files.items()}
    context = hashlib.sha256(b"".join((ROOT / p).read_bytes()
        for p in ["lean-toolchain", "lakefile.toml", "lake-manifest.json"])).hexdigest()
    users = {name: set() for name in files}
    for name, imports in deps.items():
        for imported in imports:
            users[imported].add(name)
    priorities = {}
    for name in reversed(sequence):
        priorities[name] = 1 + max((priorities[user] for user in users[name]), default=0)
    logs = ROOT / "tmp/organization-build"
    logs.mkdir(parents=True, exist_ok=True)
    state_path = logs / "state.json"
    state = {"context": context, "builds": {}}
    if args.resume and state_path.exists():
        previous = json.loads(state_path.read_text(encoding="utf-8"))
        if previous.get("context") == context:
            state = previous
    valid = {name for name in files if state["builds"].get(name, {}).get("sha256") == hashes[name]
             and state["builds"][name].get("exit_code") == 0}
    invalid = set(files) - valid
    for name in sequence:
        if deps[name] & invalid:
            invalid.add(name)
    done = set(files) - invalid
    for name in invalid:
        state["builds"].pop(name, None)
    state["modules"] = len(files)

    def save():
        temporary = state_path.with_suffix(".new.json")
        with temporary.open("w", encoding="utf-8", newline="\n") as output:
            json.dump(state, output, indent=2)
            output.write("\n")
        temporary.replace(state_path)

    save()
    toolchain = (ROOT / "lean-toolchain").read_text().strip().replace("/", "--").replace(":", "---")
    native = Path.home() / ".elan/toolchains" / toolchain / "bin/lake.exe"
    lake = str(native) if native.exists() else shutil.which("lake")
    if not lake:
        parser.error("Lake is not available")
    env = os.environ.copy()
    env["LEAN_NUM_THREADS"] = "1"
    flags = subprocess.CREATE_NO_WINDOW if os.name == "nt" else 0
    progress = SimpleQueue()
    success = re.compile(r"^[✔⚠] \[\d+/\d+\] (?:Built|Replayed) "
                         r"(LeanTrominoes(?:\.[A-Za-z0-9_]+)*)(?:\s|$)")

    def build(names, number):
        log = logs / f"module-{number:05d}.log"
        start = time.monotonic()
        with log.open("w", encoding="utf-8") as output:
            process = subprocess.Popen([lake, "--no-ansi", "--fail-fast", "build"]
                + ["+" + name + ":olean" for name in names],
                cwd=ROOT, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                text=True, encoding="utf-8", creationflags=flags)
            for line in process.stdout:
                output.write(line)
                output.flush()
                match = success.match(line)
                if match and match[1] in names:
                    progress.put((match[1], round(time.monotonic() - start, 1), log))
            code = process.wait()
        return code, round(time.monotonic() - start, 1), log

    pending = set(files) - done
    running = {}
    failed = False
    number = len(list(logs.glob("module-*.log")))
    print(f"Building {len(files)} modules; {len(done)} completed; "
          f"at most {args.workers} compiler processes; batches of {args.batch_size}.", flush=True)

    def succeeded(name, seconds, log):
        if name in done:
            return False
        state["builds"][name] = {"exit_code": 0, "sha256": hashes[name],
            "seconds": seconds, "log": str(log.relative_to(ROOT))}
        done.add(name)
        print(f"BUILD {len(done)}/{len(files)} ({seconds}s): {name}", flush=True)
        return True

    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        while pending or running:
            if not failed:
                ready = sorted((name for name in pending if deps[name] <= done),
                               key=lambda name: (-priorities[name], name))
                while ready and len(running) < args.workers:
                    names = ready[:args.batch_size]
                    del ready[:args.batch_size]
                    pending.difference_update(names)
                    number += 1
                    running[pool.submit(build, names, number)] = names
            if not running:
                break
            completed, _ = wait(running, timeout=0.5, return_when=FIRST_COMPLETED)
            changed = False
            while True:
                try:
                    name, seconds, log = progress.get_nowait()
                except Empty:
                    break
                changed = succeeded(name, seconds, log) or changed
            for future in completed:
                names = running.pop(future)
                code, seconds, log = future.result()
                if code:
                    failed = True
                    changed = True
                    for name in names:
                        state["builds"][name] = {"exit_code": code, "sha256": hashes[name],
                            "seconds": seconds, "log": str(log.relative_to(ROOT))}
                    print(f"FAILED {', '.join(names)}: {log.relative_to(ROOT)}", flush=True)
                    print(log.read_text(encoding="utf-8")[-16000:], flush=True)
                else:
                    for name in names:
                        changed = succeeded(name, seconds, log) or changed
            if changed:
                save()
    if failed or len(done) != len(files):
        print(f"Build incomplete: {len(done)}/{len(files)} modules; see {logs}", flush=True)
        return 1
    print(f"All {len(files)} modules built; checking the ordinary Lake build.", flush=True)
    return subprocess.run([lake, "build"], cwd=ROOT, env=env, creationflags=flags).returncode


if __name__ == "__main__":
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8")
    sys.exit(main())
