"""Certify I-completion gadgets with equality guards on both boundaries.

Each minor and clause has height 27. The copy has height 54. These guards
preserve the original truth tables and expose the same boundary geometry.
The shared generator produces Lean-checked tilings and exclusion certificates.
"""
import sys
from completion_pattern_data import ROOT, generate


def read(name):
    rows = (ROOT / 'data/completion/I' / (name + '.asc')).read_text().splitlines()
    while not rows[0].strip():
        rows.pop(0)
    while not rows[-1].strip():
        rows.pop()
    return {(x, y): c for y, row in enumerate(rows) for x, c in enumerate(row) if c != ' '}


def guarded(name):
    layers = 2 if name == 'dup' else 1
    width = 36 if name in ['dup', 'TFTSAT'] else 18
    result = {}

    def append(atom, dx, dy):
        for (x, y), c in read(atom).items():
            p = (x + dx, y + dy)
            assert p not in result or result[p] == '?' or c == '?'
            if p not in result or c != '?':
                result[p] = c

    for row in range(layers):
        for x in range(0, width, 18):
            append('eq', x, 9 * row)
    append(name, 0, 9 * layers)
    bottom = 9 * layers + (18 if name == 'dup' else 9)
    for row in range(layers):
        for x in range(0, width, 18):
            append('eq', x, bottom + 9 * row)
    return result


if __name__ == '__main__':
    for name in sys.argv[1:] or ['eq', 'neg', 'plug-top', 'plug-bot', 'dup', 'TFTSAT']:
        generate('I', 'guarded-' + name, full_boundary=name not in ['dup', 'TFTSAT'], grid=guarded(name), fast=True,
                 region_atom={'dup': 'copy', 'TFTSAT': 'clause'}.get(name))
