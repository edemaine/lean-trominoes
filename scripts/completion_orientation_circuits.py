"""Generate candidate orientation circuits and Lean truth-table certificates.

Search/graph construction is untrusted; generated certificates are checked
by the Lean kernel. Geometric circuit correctness is proved separately.
"""
from collections import defaultdict, deque
from itertools import product

SIZE = 64
DIRECTIONS = ((0,-1),(1,0),(-1,0),(0,1))
OPPOSITE = (3,2,1,0)
TERMINALS = ((32,0),(63,32),(0,32),(32,63))

class Macro:
    def __init__(self):
        self.classes = {}
        self.ports = defaultdict(set)
        self.clauses = {}
        self.terminals = {}
    def clause(self, point, label):
        assert point not in self.classes
        self.clauses[point] = label
    def wire(self, name, *corners):
        points = [corners[0]]
        for end in corners[1:]:
            x,y = points[-1]
            assert x == end[0] or y == end[1]
            dx = (end[0]>x)-(end[0]<x)
            dy = (end[1]>y)-(end[1]<y)
            while (x,y) != end:
                x,y = x+dx,y+dy
                points.append((x,y))
        for p in points:
            assert 0 <= p[0] < SIZE and 0 <= p[1] < SIZE
            if p not in self.clauses:
                assert self.classes.get(p,name) == name, (p,name,self.classes.get(p))
                self.classes[p] = name
        for a,b in zip(points,points[1:]):
            d = DIRECTIONS.index((b[0]-a[0],b[1]-a[1]))
            self.ports[a].add(d)
            self.ports[b].add(OPPOSITE[d])
    def terminal(self, side, name, *corners):
        self.wire(name, TERMINALS[side], *corners)
        self.ports[TERMINALS[side]].add(side)
        self.terminals[side] = name
    def xor(self, left, right, center=(16,32), halfwidth=8, halfheight=8):
        x,y = center
        top,bot = (x,y-halfheight),(x,y+halfheight)
        self.clause(top,23)
        self.clause(bot,20)
        self.wire(left,(x-halfwidth,y),(x-halfwidth,y-halfheight),top)
        self.wire(left,(x-halfwidth,y),(x-halfwidth,y+halfheight),bot)
        self.wire(right,(x+halfwidth,y),(x+halfwidth,y-halfheight),top)
        self.wire(right,(x+halfwidth,y),(x+halfwidth,y+halfheight),bot)
    def label(self,p):
        return self.clauses.get(p,sum(1 << (3-d) for d in self.ports[p]))
    def validate(self):
        for p,ds in list(self.ports.items()):
            if p in self.clauses:
                assert ds <= {0,1,2}, (p,ds)
            for d in ds:
                q = (p[0]+DIRECTIONS[d][0],p[1]+DIRECTIONS[d][1])
                if 0 <= q[0] < SIZE and 0 <= q[1] < SIZE:
                    assert OPPOSITE[d] in self.ports[q], (p,d,q)
                else:
                    assert self.terminals.get(d) == self.classes[p]
        for name in set(self.classes.values()):
            members = {p for p,v in self.classes.items() if v == name}
            root = next(iter(members))
            seen = {root}; queue = deque([root])
            while queue:
                p = queue.popleft()
                for d in self.ports[p]:
                    q = (p[0]+DIRECTIONS[d][0],p[1]+DIRECTIONS[d][1])
                    if q in members and q not in seen:
                        seen.add(q); queue.append(q)
            assert members == seen, (name,len(members),len(seen))
        for p in self.clauses:
            for d in (0,1,2):
                q=(p[0]+DIRECTIONS[d][0],p[1]+DIRECTIONS[d][1])
                assert q not in self.clauses
    def formula(self,values):
        for p,label in self.clauses.items():
            inputs=[]
            for d in (0,1,2):
                q=(p[0]+DIRECTIONS[d][0],p[1]+DIRECTIONS[d][1])
                bit = values[self.classes[q]] if OPPOSITE[d] in self.ports[q] else False
                positive = ((label-16) >> (2-d)) & 1
                inputs.append(bit if positive else not bit)
            if not any(inputs): return False
        return True
    def states(self):
        names=sorted(set(self.classes.values()))
        accepted=set()
        for bits in product((False,True),repeat=len(names)):
            values=dict(zip(names,bits))
            if self.formula(values):
                accepted.add(tuple(values[self.terminals[d]] if d in self.terminals else False for d in range(4)))
        return accepted

def make(kind):
    m=Macro()
    if kind == 'blank': pass
    elif kind in ('horizontal','vertical','northwest','southeast'):
        sides={'horizontal':(1,2),'vertical':(0,3),'northwest':(0,2),'southeast':(1,3)}[kind]
        for d in sides: m.terminal(d,'A',(32,32))
    elif kind == 'northeast':
        m.xor('A','B',center=(32,32))
        m.terminal(0,'A',(32,16),(24,16),(24,32))
        m.terminal(1,'B',(40,32))
    elif kind == 'southwest':
        m.xor('A','B',center=(32,32))
        m.terminal(2,'A',(24,32))
        m.terminal(3,'B',(32,48),(40,48),(40,32))
    elif kind == 'copy':
        m.xor('W','A')
        m.terminal(2,'W',(8,32))
        m.wire('A',(24,32),(32,32))
        m.terminal(0,'A',(32,32))
        m.terminal(1,'A',(32,32))
    elif kind == 'exactone':
        m.clause((32,24),23)
        for p in ((16,8),(48,8),(32,40)): m.clause(p,20)
        m.wire('A',(16,24),(32,24))
        m.wire('B',(32,8),(32,24))
        m.wire('C',(48,24),(32,24))
        m.wire('A',(16,24),(16,20),(12,20),(12,8),(16,8))
        m.wire('B',(32,8),(16,8))
        m.wire('B',(32,8),(48,8))
        m.wire('C',(48,24),(48,20),(52,20),(52,8),(48,8))
        m.wire('A',(16,24),(16,40),(32,40))
        m.wire('C',(48,24),(48,40),(32,40))
        m.xor('W','A',center=(8,32),halfwidth=6,halfheight=6)
        m.terminal(2,'W',(2,32))
        m.wire('A',(14,32),(16,32))
        m.terminal(0,'B',(32,8))
        m.terminal(1,'C',(56,32),(56,24),(48,24))
    else: raise ValueError(kind)
    m.validate()
    return m

def expected(kind,b):
    n,e,w,s=b
    active={'blank':(), 'horizontal':(1,2),'vertical':(0,3),'northwest':(0,2),
            'southeast':(1,3),'northeast':(0,1),'southwest':(2,3),'copy':(0,1,2),'exactone':(0,1,2)}[kind]
    if any(b[d] for d in range(4) if d not in active): return False
    return {'blank':True,'horizontal':e==w,'vertical':n==s,'northwest':n==w,
            'southeast':s==e,'northeast':n!=e,'southwest':s!=w,'copy':(not w)==n==e,
            'exactone':int(not w)+int(n)+int(e)==1}[kind]


KINDS = ('blank','horizontal','vertical','northwest','southeast','northeast','southwest','copy','exactone')
CLASS_NAMES = ('A','B','C','W')

def option(value):
    return 'none' if value is None else f'some {value}'

def node_data(m):
    nodes=[]
    anchors=[0]*4
    clause_positions=sorted(m.clauses,key=lambda p:(p[1],p[0]))
    for p in clause_positions:
        signals=[]
        for d in range(4):
            q=(p[0]+DIRECTIONS[d][0],p[1]+DIRECTIONS[d][1])
            signals.append(CLASS_NAMES.index(m.classes[q]) if d < 3 and OPPOSITE[d] in m.ports[q] else None)
        nodes.append((p,m.clauses[p],signals,None,None,0,0))
    for k,name in enumerate(CLASS_NAMES):
        members={p for p,v in m.classes.items() if v == name}
        if not members: continue
        terminals=[TERMINALS[d] for d,v in sorted(m.terminals.items()) if v == name]
        root=terminals[0] if terminals else min(members)
        anchors[k]=len(nodes)
        seen={root}; queue=deque([(root,None,0)])
        while queue:
            p,parent,parent_port=queue.popleft()
            index=len(nodes)
            signals=[k if d in m.ports[p] else None for d in range(4)]
            nodes.append((p,m.label(p),signals,k,parent,parent_port,min(m.ports[p])))
            for d in sorted(m.ports[p]):
                q=(p[0]+DIRECTIONS[d][0],p[1]+DIRECTIONS[d][1])
                if q in members and q not in seen:
                    seen.add(q); queue.append((q,index,OPPOSITE[d]))
        assert members == seen
    return nodes,anchors,len(clause_positions)

def generate():
    from pathlib import Path
    root=Path(__file__).resolve().parent.parent
    target=root/'LeanTrominoes'
    for kind in KINDS:
        m=make(kind)
        wanted={b for b in product((False,True),repeat=4) if expected(kind,b)}
        assert m.states() == wanted
        nodes,anchors,count=node_data(m)
        name=kind.title()
        lines=['/- Generated by scripts/completion_orientation_circuits.py. -/',
               'import LeanTrominoes.CompletionCircuit','',
               'noncomputable section',
               f'namespace LeanTrominoes.CompletionPattern.LBricks.CircuitData.{name}',
               '', 'def circuit : Circuit where','  nodes := [']
        records=[]
        for p,label,signals,wire,parent,parent_port,read_port in nodes:
            records.append(f'    ⟨({p[0]},{p[1]}),{label},['+', '.join(map(option,signals))+f'],{option(wire)},{option(parent)},{parent_port},{read_port}⟩')
        lines += [(','+chr(10)).join(records)+']',f'  clauseCount := {count}',
                  '  anchors := ['+','.join(map(str,anchors))+']',
                  '  terminals := ['+','.join(option(CLASS_NAMES.index(m.terminals[d])) if d in m.terminals else 'none' for d in range(4))+']',
                  '',f'end LeanTrominoes.CompletionPattern.LBricks.CircuitData.{name}','']
        (target/f'CompletionCircuit{name}Data.lean').write_text(chr(10).join(lines),encoding='utf8',newline=chr(10))
        print(kind,len(nodes),count,len(wanted))
    lines=['/- Generated by scripts/completion_orientation_circuits.py. -/']
    lines += [f'import LeanTrominoes.CompletionCircuit{k.title()}Data' for k in KINDS]
    lines += ['', 'noncomputable section','namespace LeanTrominoes.CompletionPattern.LBricks',
              '', 'set_option Elab.async false','set_option maxHeartbeats 0','set_option maxRecDepth 65536','',
              'def circuitFor : CircuitKind → Circuit']
    lines += [f'  | .{k} => CircuitData.{k.title()}.circuit' for k in KINDS]
    lines += ['', '/-- Exact terminal truth tables for the nine orientation-cell circuits. -/',
              'theorem circuit_truth_table (kind : CircuitKind) : (circuitFor kind).TruthTableCorrect kind := by',
              '  cases kind <;> decide +kernel','',
              'end LeanTrominoes.CompletionPattern.LBricks','']
    (target/'CompletionCircuitTruthTables.lean').write_text(chr(10).join(lines),encoding='utf8',newline=chr(10))

if __name__ == '__main__':
    generate()
