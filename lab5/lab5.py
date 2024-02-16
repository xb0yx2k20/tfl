import sys
import pandas as pd


class Grammar:
    def __init__(self, path: str):
        self.g = self.parse_rules(path)
        self.NT = self.g.keys()
        assert 'S' in self.NT, 'There is no start symbol'

        self.T = self.get_terminals()
        self.FIRST = {}
        self.FOLLOW = {}
        self.table = {term: {nterm: [] for nterm in self.NT}
                      for term in self.T}
        self.compute_FIRST()
        self.compute_FOLLOW()
        # self.construct_table()

    def print_table(self):
        df = pd.DataFrame(self.table)
        df = df.reindex(sorted(df.columns, reverse=True), axis=1)
        print(df)

    def construct_table(self):
        for A in self.NT:
            for r in self.g[A]:
                lst_fst = self.compute_FIRST_list(r.split(' '))
                for t in lst_fst:
                    if t in self.NT or t == '!':
                        continue
                    self.table[t][A].append([f'{r}'])
                if '!' in lst_fst:
                    for t in self.FOLLOW[A]:
                        if t in self.NT:
                            continue
                        self.table[t][A].append('!')

    def get_terminals(self):
        res = set()
        for A in self.NT:
            for r in self.g[A]:
                res = res.union(
                    {x for x in r.split(' ') if x not in self.NT and x != '!'})
        return res.union('$')

    def compute_FIRST(self):
        for A in self.NT:
            self.FIRST[A] = set()
        changed = True
        while changed:
            changed = False
            for A in self.NT:
                for r in self.g[A]:
                    r_fst = self.T_FIRST([r], A)
                    if len(self.FIRST[A].intersection(r_fst)) != len(r_fst):
                        self.FIRST[A] = self.FIRST[A].union(r_fst)
                        changed = True
        return

    def T_FIRST(self, t, last=None):
        if isinstance(t, list):
            res = set()
            for alt in t:
                alt_split = alt.split(' ')
                tmp = self.T_FIRST(alt_split[0], last)
                res = res.union(tmp)
                if '!' in tmp:
                    res = res.union(self.T_FIRST(alt_split[1:], last))
            return res
        if t not in self.NT:
            return {t}
        else:
            nr = list(filter(lambda x: x != last, self.g[t]))
            return self.T_FIRST(nr, t)

    def compute_FIRST_list(self, y, last):
        if isinstance(y, list):
            if y == []:
                return {'!'}
            k = 1
            n = len(y)
            k_fst = self.T_FIRST(y[0], last)
            tmp = k_fst
            while '!' in k_fst and k < n:
                k_fst = self.T_FIRST(y[k], last)
                tmp = tmp.union(k_fst - {'!'})
                k += 1
            if '!' in k_fst:
                tmp = tmp.union({'!'})
            return tmp
        elif y in self.NT:
            return self.FIRST[y]
        else:
            return y

    def compute_FOLLOW(self):
        for A in self.NT:
            self.FOLLOW[A] = set()
        self.FOLLOW["S"] = {"$"}
        changed = True
        while changed:
            changed = False
            for A in self.NT:
                for r in self.g[A]:
                    r_split = r.split(' ')
                    for i, x in enumerate(r_split):
                        if x not in self.NT:
                            continue
                        new_set = self.compute_FIRST_list(r_split[i + 1:], x)
                        tmp = self.FOLLOW[x]
                        self.FOLLOW[x] = self.FOLLOW[x].union(
                            new_set - {'!'}
                        )
                        if '!' in new_set:
                            self.FOLLOW[x] = self.FOLLOW[x].union(
                                self.FOLLOW[A]
                            )
                        changed = self.FOLLOW[x] != tmp

    def remove_useless(self, g: dict):
        gen = set()
        for A, r in g.items():
            for alt in r:
                if not any(filter(lambda x: x in g.keys(), alt)):
                    gen.add(A)
                    break
        changed = True
        while changed:
            changed = False
            for A, r in g.items():
                for alt in r:
                    if all(x in gen for x in alt.split(' ') if x in g.keys()):
                        if A not in gen:
                            gen.add(A)
                            changed = True
        for A in list(g):
            r = g[A]
            if A not in gen or any(x not in gen and x in g.keys() for x in
                                   [x for xs in r for x in xs.split(' ')]):
                del g[A]
        return g

    def parse_rules(self, path: str):
        rules = {}
        with open(path, 'r') as f:
            for line in f.read().splitlines():
                l, r = line.split(' -> ')
                r = r.split(' | ')
                if l in rules:
                    rules[l].extend(r.split(' '))
                else:
                    rules[l] = r
        rules = self.remove_useless(rules)

        return rules

    def parse(self, w: str):
        # просто LL(1)
        w += ' $'
        w = w.split(' ')
        s = ['S']
        i = 0
        while len(s) > 0:
            if i >= len(w):
                print(f'Parsing error. Stack {s} is not empty.')
                return
            A = s[-1]
            r = w[i]
            print(s, r)
            if A in self.T or A == '$':
                if A == r:
                    s.pop()
                    i += 1
                else:
                    print(
                        f'Parse error in position {i}. Expected {r} but found {A}.')
                    return
            elif A in self.NT:
                elem = []
                if r in self.table:
                    elem = self.table[r][A]
                else:
                    print(
                        f'Parse error in position {i}. {r} not in terminals.')
                    return
                if elem == []:
                    print(
                        f'Parse error in position {i}. Table[{r}][{A}] is empty.')
                    return
                s.pop()
                s.extend(
                    filter(
                        lambda x: x != '!',
                        reversed(
                            elem[0].split(' '))))
        print('Successful parsing')


step = 0
first_split = -1


class Node:
    def __init__(self, l):
        self.label = l
        self.children = []

    def add_children(self, child):
        self.children.append(child)

    def __repr__(self):
        return f'Node {self.label}, {self.children}'


class SharedNode:
    def __init__(self, tp: str, l, i, j):
        self.type = tp
        if tp == 'packed':
            self.label = (l, i)
        else:
            self.label = (l, i, j)
        self.children = []

    def add_child(self, child):
        self.children.append(child)

    def __repr__(self):
        return f'Type: {self.type}, Children: {self.children}'


class GraphStructuredStack:
    def __init__(self):
        self.graph = {}
        self.P = {}

    def __getitem__(self, l) -> Node:
        if l not in self.graph:
            self.add_node(l)
        return self.graph[l]

    def add_node(self, l):
        if l in self.graph:
            print(f'Warning! {l} is already in graph!')
        self.graph[l] = Node(l)
        self.P[l] = []

    def add_trans(self, l, j: str):
        self.P[l].append(j)

    def get_nodes(self, l):
        return self.P[l]


class SharedPPForest:
    def __init__(self):
        self.nodes = {}

    def __getitem__(self, k: list):
        l, i, j = k
        if (l, i, j) in self.nodes:
            return self.nodes[(l, i, j)]
        elif isinstance(l, str):
            node = SharedNode('symbol', l, i, j)
        elif l is None:
            node = SharedNode('dummy', l, i, j)
        elif len(l) == 3:
            node = SharedNode('inter', l, i, j)
        else:
            assert False, 'Unknown node type'
        self.nodes[(l, i, j)] = node
        return node


class GLLParser:
    def __init__(self, grammar):
        self.stack = GraphStructuredStack()
        self.SPPFS = SharedPPForest()
        self.grammar = grammar
        self.w = ''
        self.R = []
        self.U = []
        self.I = ''
        self.m = 0

    def test(self, y, A, a):
        if a in self.grammar.NT:
            a_fst = self.grammar.FIRST[a]
        else:
            a_fst = self.grammar.T_FIRST(a[0][0])
        return y in a_fst or ('!' in a_fst and y in self.grammar.FOLLOW[A])

    def has_child(self, y, l):
        for c in y.children:
            if c.label == l:
                return True
        return False

    def getNodeT(self, x, i):
        if x is None:
            h = i
        else:
            h = i + 1
        return self.SPPFS[(x, i, h)]

    def getNodeP(self, L, w, z):
        X, alt, pos = L
        n = len(self.grammar.g[X][alt].split(' '))
        alpha = self.grammar.g[X][alt].split(' ')[:pos]
        if len(alpha) == 1 and pos != n:
            return z
        elif pos == n:
            t = X
        else:
            t = L
        _, kz, i = z.label
        _, j, _ = w.label
        if w.type != 'dummy':
            y = self.SPPFS[(t, j, i)]
            if not self.has_child(y, (L, kz)):
                node = SharedNode('packed', L, kz, None)
                node.add_child(w)
                node.add_child(z)
                y.add_child(node)
        else:
            y = self.SPPFS[(t, kz, i)]
            if not self.has_child(y, (L, kz)):
                node = SharedNode('packed', L, kz, None)
                node.add_child(z)
                y.add_child(node)
        return y

    def add(self, L, u, i, w):
        if (L, u, w) not in self.U[i]:
            self.U[i].append((L, u, w))
            self.R.append((L, u, i, w))

    def create(self, L, cu, j, w):
        v = self.stack[(L, j)]
        trans = [n for n, l in v.children if n.label == cu.label and l == w]
        if len(trans) == 0:
            v.add_children((cu, w))
            for z in self.stack.P[v.label]:
                y = self.getNodeP(L, w, z)
                self.add(L, cu, z.label[-1], y)
        return v

    def pop(self, cu, i, z):
        if cu != self.stack[('L0', 0)]:
            L, _ = cu.label
            self.stack.add_trans(cu.label, z)
            for v, w in cu.children:
                y = self.getNodeP(L, w, z)
                self.add(L, v, i, y)
        return cu

    def parse(self, w: str):
        global step
        pass

    def print_current_stack(self):
        print(self.SPPFS.nodes)


class GLLParserBuilder:
    def __init__(self, grammar):
        self.grammar = grammar

    def code_nonterm(self, A, n, j, l, X):
        if j == l:
            L = "'L1'"
        else:
            L = f"('{A}',{n},{j+1})"
        return '''\
        elif L ==  ('%s',%d,%d):
            step += 1
            cu = self.create(%s, cu, i, cn)
            L = '%s'
            continue
    ''' % (A, n, j, L, X)

    def code_term(self, A, n, j, l, X):
        if j == l:
            L = "'L1'"
        else:
            L = f"('{A}',{n},{j+1})"
        return '''\
        elif L == ("%s",%d,%d):
            if self.I[i] == '%s':
                cr = self.getNodeT(self.I[i], i)
                i += 1
                L = %s
                cn = self.getNodeP(L, cn, cr)
            else:
                L = 'L0'
            continue
    ''' % (A, n, j, X, L)

    def code_eps(self, A, n):
        return '''\
        elif L == ("%s", %d, 0):
            cr = self.getNodeT(None, i)
            cn = self.getNodeP(L, cn, cr)
            L = 'L1'
            continue
    ''' % (A, n)

    def code(self, A, n, rule):
        res = []
        rr = rule.split(' ')
        if not rr:
            r = self.code_eps(A, n)
            res.append(r)
        else:
            i = 0
            while i < len(rr):
                t = rr[i]
                if t == '!':
                    i += 1
                    continue
                if t in self.grammar.NT:
                    r = self.code_nonterm(A, n, i, len(rr), t)
                else:
                    r = self.code_term(A, n, i, len(rr), t)
                res.append(r)
                i += 1
            if rr == ['!']:
                rlen = len(rr) - 1
            else:
                rlen = len(rr)
            res.append('''\
        elif L == ('%s',%d,%d):
            L = 'L1'
            continue
    ''' % (A, n, rlen))
        return '\n'.join(res)

    def code_rules(self, A, rules):
        res = []
        res.append('''\
        elif L == '%s':
    ''' % A)
        for n, _ in enumerate(rules):
            res.append('''\
            step += 1
            self.add( ('%s',%d,0), cu, i, SharedNode('dummy', '$', 0, 0) )''' % (A, n))

        res.append('''\
            L = 'L0'
            continue''')
        for n, alt in enumerate(rules):
            # print(alt)
            r = self.code(A, n, alt)
            res.append(r)
        return '\n'.join(res)

    def get_parser(self):
        res = ['''
def parse(self, w):
    global step, first_split
    self.m = len(w)
    self.I = w + '$'
    self.R = []
    self.U = [[] for _ in range(self.m+1)]
    L = 'S'
    cu, cn = self.stack[('L0', 0)], SharedNode('dummy', '$', 0, 0)
    i = 0

    while True:
        if step == int(sys.argv[1]):
            print(self.SPPFS.nodes)
            step += 10
        #print(L, step, self.SPPFS.nodes)
        if L == 'L0':
            if self.R:
                L, cu, i, cn = self.R[0]
                self.R = self.R[1:]
                continue
            else:
                first_split = i
                return ('S', 0, self.m) in self.SPPFS.nodes
        elif L == 'L1':
            step += 1
            cu = self.pop(cu, i, cn)
            L = 'L0'
            continue
    ''']
        for A in self.grammar.NT:
            r = self.code_rules(A, self.grammar.g[A])
            res.append(r)
        res.append("""
        else:
            return False
        """)

        algorithm = '\n'.join(res)
        p = GLLParser(self.grammar)
        exec(algorithm, globals(), locals())
        p.parse = locals()['parse'].__get__(p)
        return p


if __name__ == '__main__':
    if len(sys.argv) > 1:
        grammar = Grammar('grammar.txt')
        builder = GLLParserBuilder(grammar)
        parser = builder.get_parser()
        parsed = parser.parse(sys.argv[2])
        if not parsed:
            print(f'Failed! Error at {first_split}')
        else:
            print('Sucess')
    else:
        print('Missing arguments')
