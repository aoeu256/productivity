import collections
from io import StringIO

# from __future__ import print_function
from collections import namedtuple
from contextlib import contextmanager
import doctest, ast, sys
from itertools import chain

from ast import Name, Tuple, Expression, Assert, \
    Assign, AugAssign, Del, Return, Yield, Raise, Global, \
    If, While, For, With, FunctionDef, ClassDef, \
    Lambda, ListComp, SetComp, DictComp, GeneratorExp
import inspect
import functools
import tokenize
import token
import pprint
import ast
import collections
import pdb
import traceback
import astor
# import debug
# pydevd.GetGlobalDebugger().setExceptHook(Exception, True, False)

@contextmanager
def ignored(exc):
    try:
        yield
    except exc:
        pass

# with query('~f(*~args)') as query:
# 	query.add_next()

# static locals
#
# def query(q, code):
#     """
# >>> for node in query('~f(*~args)', 'for g in c: a(b(5)); c(8)'):
# ...    print(tos(node))
# a(b(5))
# b(5)S
# c(8)
#     """
#     sStr = '_q_u_e_'
#     assert sStr not in q
#     q.replace('~', sStr)
#     locs = {}
#     pt = ast.parse(q)
#     for node in pt.walk(q):
#         if node.__class__ != pt.__class__: continue
#
#         # updateLocs(node, locs)
#
#         for fielda, fieldb in zip(ast.iter_fields(node), ast.iter_fields(q)):
#             if fielda == fieldb or fieldb == sStr: break
#
#         yield node


class Context(dict):
    def __init__(self, v=None):
        self._items = []
        if v is not None:
            self._items.append(v)

    def __getitem__(self, k):
        for d in reversed(self._items):
            with ignored(KeyError):
                return d[k]
        raise KeyError(k)

    def __setitem__(self, k, v):
        try:
            self._items[-1][k] = v
        except IndexError:
            self._items.append({k: v})

    def __contains__(self, k):
        return any(k in d for d in self._items)

    def push(self, d):
        self._items.append(d)

    def pop(self):
        return self._items.pop()

    def all_keys(self):
        return chain(*(i.keys() for i in self._items))

    def all_pairs(self):
        return chain(*(i.items() for i in self._items))

    @contextmanager
    def local(self, d):
        self._items.append(d)
        yield self._items[-1]
        self._items.pop()

    def __repr__(self):
        return self._items.__repr__()

    def clear(self):
        self._items[:] = []


def tonamedtuple(obj):
    np = namedtuple(obj.__class__.__name__, obj.__dict__.keys())
    return np(**obj.__dict__)


def fullName(node):
    """
>>> fullName(ast.parse('b.a.c').body[0].value)
'b.a.c'
    """
    if isinstance(node, ast.Name):
        return node.id
    elif isinstance(node, ast.Attribute):
        return fullName(node.value) + '.' + node.attr


def leftName(node):
    """
>>> leftName(ast.parse('b.a.c').body[0].value)
'b'
    """
    if isinstance(node, ast.Name):
        return node.id
    elif isinstance(node, ast.Attribute):
        return leftName(node.value)


def is_name(node):
    return isinstance(node, ast.Name) or isinstance(node, ast.Attribute)


tos = lambda x: astor.to_source(x)


class PrettyNode(object):
    def __init__(self, node):
        self.node = node

    def __repr__(self):
        return tos(self.node)

    def __getattr__(self, v):
        return getattr(self.node, v)


def prettify(node):
    # for nade in ast.walk(node):
    # 		nade = PrettyNode(nade)
    node = PrettyNode(node)
    return node


def get_names(node):
    if isinstance(node, Name):
        return [node]
    elif isinstance(node, Tuple):
        return node.elts


def lnames(node):
    for targ in node.targets:
        for name in get_names(targ):
            yield name

class DepFinder(ast.NodeVisitor):
    """
>>> code = ['lst=range(25)','def fn(a): return a+b+c', 'random.choice(fn(lst))']
>>> df = DepFinder()
>>> def dodeps(s): dep = df.get_deps(s); return DepFinder.tup(dep.new, list(sorted(dep.deps)) 
>>> dodeps(code[1])
deps(new=['fn'], deps=['c', 'b'])

>>> dodeps(code[2])
deps(new=[], deps=['fn', 'lst', 'random'])

>>> set(dodeps('a, b = c, d = 2, 2').new) == {'a', 'b', 'c', 'd'}
True

>>> dodeps('[(a, i) for i in range(20)]')
deps(new=[], deps=['a'])

>>> dodeps('for b in [0]: f(b+c)')
deps(new=[], deps=['c', 'f'])
    """
    depstatements = set([Expression, Assert, Assign, AugAssign,
                         Del, Return, Yield, Raise, Global])
    compound = set([If, While, For,  With, FunctionDef, ClassDef])
    statements = compound | depstatements

    tup = namedtuple('deps', ['new', 'deps'])
    fulltup = namedtuple('deps', ['new', 'deps', 'nodes'])

    def __init__(self):
        self.args = Context()
        # self.localDeps = Context() # {node: [name]}
        self.deps = set()
        self.setters = Context()  # {name: [node]}
        # self.globals = set(chain(dir(__builtins__), globals(), sys.modules))
        self.globals = set(__builtins__)
        self.classes = set()
        self.parents = []  # Combine the deps of the CHILDREN!
        self.scope = []
        self.alldeps = {}
        self.curdeps = {}
        self.importdeps = []
        self.scope2deps = {}

    # self.scopedir = {}
    def short_deps(self, node):  # only one setter allowed
        self.visit(ast.parse(node))
        return DepFinder.tup(list(self.setters.all_keys()), self.deps)

    def full_deps(self, node):
        self.visit(ast.parse(node))
        ak = (k for k, v in self.setters.all_pairs())
        av = (v for k, v in self.setters.all_pairs())
        return DepFinder.fulltup(list(ak), self.deps, list(av))

    def get_deps(self, node, func=None):
        if func is None: func = self.short_deps
        self.deps.clear()
        self.setters.clear()
        return func(node)

    def add_dep(self, node):  # name should be fullName
        if self.is_depvar(node):
            name = leftName(node)
            if name not in self.setters:
                self.deps.add(name)
        elif leftName(node) in sys.modules:
            self.importdeps.append(node)

    def add_setter(self, name, node):  # name should be fullName
        node = prettify(node)
        try:
            self.setters[name].append(node)
        except KeyError:
            self.setters[name] = [node]

    def debugdeps(self, node):
        return self.curdeps[node], tos(node)

    def is_depvar(self, node):
        return not (leftName(node) in self.args \
                    or leftName(node) in self.globals)

    def generic_visit(self, node):
        for node in node.body:
            self.visit_deps(node)

    def visit_children(self, node):
        if isinstance(node, list):
            for node in node:
                self.visit_deps(node)
        else:
            for node in ast.iter_child_nodes(node):
                self.visit_deps(node)

    def ns_name(self, node):
        return '.'.join(self.scope) + fullName(node)

    def visit_deps(self, node):
        if isinstance(node, ast.Assign):
            targets = {fullName(name): set([])
                for tags in node.targets
                for name in get_names(tags)
            }

            def rvals(node):
                if is_name(node):
                    for k in targets:
                        targets[k].add(node)
                else:
                    for node in ast.iter_child_nodes(node):
                        rvals(node)

            rvals(node.value)

            for name, deps in targets.items():
                self.add_setter(name, node)
                for node in deps:
                    self.add_dep(node)
        elif isinstance(node, ClassDef):
            self.add_setter(node.name, node)
            self.visit_scoping(node, {node.name})
        elif node.__class__ in [FunctionDef, Lambda]:
            args = set(i.arg for i in node.args.args)  # Tuple argS?
            if isinstance(node, FunctionDef):
                self.add_setter(node.name, node)
                args.add(node.name)  # recursion
            self.visit_scoping(node, args)
        elif isinstance(node, For):
            names = get_names(node.target)
            self.visit_deps(node.iter)
            self.visit_scoping(node.body, {i.id for i in names})
        elif isinstance(node, With):
            args = {i.id for i in get_names(node.optional_vars)}
            self.visit_deps(node.context_expr)
            self.visit_scoping(node.body, args)
        elif node.__class__ in (ListComp, SetComp, DictComp, GeneratorExp):
            args = set([])
            for gen in node.generators:
                self.visit_scoping(gen.iter, args)
                args.update(i.id for i in get_names(gen.target))
                self.visit_scoping(gen.ifs, args)
            self.visit_scoping(node.elt, args)
        elif is_name(node):
            self.add_dep(node)
        elif isinstance(node, ast.Import):
            pass
        else:
            for nade in ast.iter_child_nodes(node):
                self.visit_deps(nade)

    def visit_scoping(self, node, args):
        with self.args.local(args):
            # with self.localDeps.local({}) as newlocals:
            with self.setters.local({}) as newsetters:
                self.visit_children(node)


def depsAll(history, depf=None):
    """
>>> depsAll(['a=2', 'b=a', 'a=b', 'b=a', 'a=b'])
linedep(linedeps={0: set(), 1: {0}, 2: {1}, 3: {2}, 4: {3}}, setters={0: ['a'], 1: ['b'], 2: ['a'], 3: ['b'], 4: ['a']}, locals={'a': 4, 'b': 3}, error=[])
    """
    depf = depf or DepFinder()
    lines = {}
    locs = {}
    setters = {}
    errors = []
    linedep = namedtuple('linedep', ['linedeps', 'setters', 'locals', 'errors'])
    for ln, line in enumerate(history):
        try:
            dep = depf.get_deps(line, func=depf.full_deps)
            localset = dep.deps & set(locs.keys())
            lines[ln] = set(locs[k] for k in localset)
            setters[ln] = dep.new  # , dep.nodes
            for k in chain(*dep.new):
                locs[k] = ln
        except SyntaxError:
            errors.append(ln)
    return linedep(lines, setters, locs, errors)


def filterdeps(linedeps, retln):
    """
    """
    deps = {}

    def findAllDeps(ln):
        with ignored(KeyError):
            deps[ln] = linedeps[ln]
            for ln in deps[ln]:
                findAllDeps(ln)

    findAllDeps(retln)

    return deps

# TODO: In order to support ';' we need to intelligently split the history up

words = lambda a: a.split() if isinstance(a, str) else list(a)

def getHistory(history):
    if history is None and '__IPYTHON__' in dir(__builtins__):
        history = _ih  # @UndefinedVariable

    newhistory = []
    for line in history:
        with ignored(SyntaxError):
            for lline in ast.parse(line).body:
                newhistory.append(astor.to_source(lline))
    return newhistory

def makefunc(name, arglist='', history=None, ret=None, imports=True):
    """
>>> hist=['b=2', 'a=b+5']
>>> print(makefunc('lol', history=hist))
def lol(b=2):
    a=b+5
    return a
>>> print(makefunc('lol', ret='b', history=hist))
def lol(b = 2):
    return b
>>> print(makefunc('lol', history=['a=4', 'def f(d): a = 5; return d + a', 'f(a)+1']))
def lol(a=4):
    def f(d): a = 5; return d + a
    return f(a)+1
    """
    history = getHistory(history)

    is_assign = lambda s: isinstance(ast.parse(s).body[0], Assign)
    foundVar = False
    if ret is None:
        lastnode = ast.parse(history[-1]).body[0]
        if isinstance(lastnode, ast.Assign):
            history.append(history[-1].split('=')[0].strip())
        ret = history[-1].strip()
        retln = len(history) - 1
        foundVar = True

    alldeps = depsAll(history)
    if not foundVar: retln = alldeps.locals[ret]

    deps = filterdeps(alldeps.linedeps, retln)
    arglines = [ln for ln, deplns in deps.items() if len(deplns) == 0 and is_assign(history[ln])]
    #arglines = [ln for ln in arglines if '=' in history[ln]]
    args = {}
    arg2ln = {}
    for ln in arglines:
        for lval in alldeps.setters[ln]:
            try:
                args[lval] = history[ln].split('=')[-1].strip()
                arg2ln[lval] = ln
            except IndexError as e:
                print(e, out=sys.stderr)

    arglist = words(arglist) or args.keys()
    funcL = ['def %s(%s):' % (name, \
                              ', '.join('%s = %s' % (k, args[k]) for k in arglist))]
    lines = sorted(ln for ln in set(deps) - set(arg2ln[i] for i in arglist) - set([retln]))
    tab = '    '
    funcL += [tab+line for ln in lines for line in history[ln].split('\n')]
    funcL.append(tab + 'return %s' % ret)
    #pprint.pprint(locals())
    return '\n'.join(funcL)

def parse(node):
    return ast.parse(node).body[0]


# def replace_tokens(s, dic={}, match=None, using=None):
# """
# >>> replace_tokens('(_+5)*_', match='_', using='a')
# '(a+5)*a' """
# 	if match is not None and using is not None:
# 		dic[match] = using
# 	s = StringIO(s)
# 	tokens = ((i[0], dic.get(i[1], i[1]), i[2], i[3], i[4])\
# 	          if i[0] == token.NAME else i \
# 	          for i in tokenize.generate_tokens(s.readline))
# 	return tokenize.untokenize(tokens)

def ap(funcdef, *args, **kwargs):
    """
    >>> fd = 'def myfunc(a, b=2, c=3, *args, **kwargs): return a + b'
    >>> ap(ast.parse(fd).body[0], 2, 3, c=5, g=1)
    {'a': 2, 'c': 5, 'b': 3, 'g': 1, 'args': (), 'kwargs': {'g': 1}}
    """
    d = {}
    fdargs = funcdef.args
    fargs = [i.arg for i in fdargs.args]

    defaults = fargs[len(fargs) - len(fdargs.defaults):]
    d.update({k: tos(v) for k, v in zip(defaults, fdargs.defaults)})
    d.update(dict(zip(fargs, args)))
    d.update(kwargs)
    if fdargs.vararg is not None:
        d[fdargs.vararg] = args[len(fargs):len(args)]
    if fdargs.kwarg is not None:
        d[fdargs.kwarg] = {k: v for k, v in kwargs.items() if k not in fargs}

    return d


def tolist(obj):
    if isinstance(obj, str):
        return obj.split()
    return obj


def bind(s, dic):
    """
>>> bind('(_+5)*_', {'_':'a'})
'((a + 5) * a)'
    """
    snode = ast.parse(s)
    for node in ast.walk(snode.body[0]):
        for field in node._fields:
            cnode = getattr(node, field)
            if isinstance(cnode, Name) and cnode.id in dic:
                setattr(node, field, parse(str(dic[cnode.id])))
    return tos(snode).replace('\n', '')


# >>> gather(history, vars='a')
# a=2
# (2+a)*2	"""
def gather(history, vars=''):
    """
>>> history = ['a=2', 'b=3', 'c=4', '_+a', '_*2']
>>> gather(history)
'((4 + 2) * 2)'"""
    keep = tolist(vars)
    newdic = {}
    mylocals = {}
    newexpr = ''
    for line in history:
        node = parse(line)
        #import bp
        if isinstance(node, ast.Expr):
            filtered_binds = {k: v for k, v in mylocals.items() if k not in keep}
            newexpr = bind(line, filtered_binds)
            mylocals['_'] = newexpr
        else:
            newdic.clear()
            exec(line, newdic)
            del newdic['__builtins__']
            if len(newdic) == 1:
                mylocals['_'] = list(newdic.values())[0]
            mylocals.update(newdic)
    return newexpr


def add(a, b): c = 8; return a + b  # @UnusedVariable


def calldic(f, *args, **kwargs):
    """
>>> calldic(add, 1, 2)
{'a': 1, 'c': 8, 'b': 2, '__retv__': 3}
    """
    d = {}
    exec
    src_locals(inspect.getsource(f)) in d
    newf = d[f.__name__]
    newf(*args, **kwargs)
    return newf.__locals__


def gensym(name):
    """
>>> gensym('a3'), gensym('a')
('a4', 'a2')
    """
    if name[-1].isdigit():
        return name[:-1] + str(int(name[-1]) + 1)
    return name + '2'


def walk_on(node, typ):
    for node in ast.walk(node):
        if isinstance(node, typ):
            yield node


def pmed(f):
    """
>>> def myadd(): b = 4; a = 2/0; c = 5
>>> pmed(myadd)()
{'b': 4}
    """

    @functools.wraps(f)
    def wrapped(*args, **kwargs):
        try:
            f()
            raise Exception("No errors")
        except Exception as e:
            loc = sys.exc_info()[2].tb_next.tb_frame.f_locals
            #loc['exc_info'] = sys.exc_info()
            return loc

    return wrapped


def src_locals(src, newvars=True):
    """
>>> print(src_locals('def add(a, b): c = 8; return a + b'))
def add(a, b):
    c = 8
    __retv__ = (a + b)
    add.__locals__ = locals()
    return (a + b)
    """
    src = ast.parse(src)
    locs = collections.OrderedDict()

    def myparser(node):

        if newvars and isinstance(node, ast.Assign):
            for name in lnames(node):
                if name.id in locs:
                    locs[name.id] = gensym(name.id)
                else:
                    locs[name.id] = name.id
            for node in walk_on(node.value, ast.Name):
                node.id = locs[name.id]
            return

        for _, node in ast.iter_fields(node):
            if isinstance(node, list):
                for nade in node:
                    if isinstance(nade, ast.Return):
                        retline = ast.parse('__retv__ = %s' % tos(nade.value)).body[0]
                        saveLocal = ast.parse(
                            ''.join([src.body[0].name, '.', '__locals__', '=', 'locals()'])).body[0]
                        node[-1:] = [retline, saveLocal] + [node[-1]]
                        break
                    else:
                        myparser(nade)
            elif isinstance(node, ast.AST):
                myparser(node)

    myparser(src.body[0])
    return tos(src)


def myadd(a, b, c=2):
    g = a + b + c
    return g + b


def parse(code):  # @DuplicatedSignature
    return ast.parse(code).body[0]


class unzip:
    def __init__(self, func, to=None, offset=0, ns=globals(), bp=[], *args, **kwargs):
        self.ln = 0
        self.bp = [0] + bp
        self.src = inspect.getsource(func)
        self.srclines = self.src.split('\n')
        self.ns = ns
        self.funcdef = ast.parse(self.src).body[0]
        applyArgs = ap(self.funcdef, *args, **kwargs)
        self.doArgs(applyArgs)
        self.run_to(to, offset)

    # 		def gen_line2node(self):
    # 			self.line2node = {0: self.funcdef}
    # 			for node in ast.walk(self.funcdef):
    # 				if node.lineno > curline:
    # 					self.line2node[node.lineno] = node
    #
    # 		gen_line2node()

    def cont(self):
        try:
            ln = (b for a, b in zip(self.bp[:1], self.bp[1:])).next()
            self.run_to(ln)
        except StopIteration:
            class NoMoreBreakPoints(Exception):
                pass

            raise NoMoreBreakPoints("no break points after line " + self.curline)

    def doArgs(self, applyArgs):
        for var, val in applyArgs.items():
            self.verbose_exec(var + '=' + val)

            # 	def iter_childs(self):
            # 		for name, field in iter_fields(node):
            # 			if isinstance(field, AST):
            # 				yield field
            # 			elif isinstance(field, list):
            # 				for item in field:
            # 					if isinstance(item, AST):
            # 						yield item

    def run_to(self, to, offset=0):
        lin = self.find(to, offset)

        start = 0 if lin < self.ln else self.ln
        if start == 0:
            self.doArgs()

        until = min(lin, len(self.srclines))

        # 		def goChild(node, topNode):
        # 			for field in iter_fields(node):
        # 				if isinstance(field, AST):
        # 					goChild(field)
        # 				elif isinstance(field, list):
        # 					for node in field:
        # 						if node.lineno <= node:
        #
        # 					self.verbose_exec(statement)

        for node in self.funcdef.body:
            if node.lineno > until:
                break

                # 		for ln in range(start, until):
                # 			self.funcdef.body
                #			self.verbose_exec(self.srclines[ln])

        self.ln = lin

    # LOGICAL LINE BITCHES!!!(TABS?), AST CAN FIX THAT SHIT?
    # SET_TRACE?
    # use parse / tos | logical lines

    ast.iter_fields

    def verbose_exec(self, statement, **pargs):
        if 'return' in statement:
            statement = tos(parse(statement).value)
        print(statement, **pargs)
        exec(statement, self.ns)

    def find(self, to, offset):
        if isinstance(to, int):
            return to + offset
        elif isinstance(to, str):
            return (n for n, text in enumerate(self.srclines)
                    if to in text).next()
        elif isinstance(to, tuple):
            return self.find(to, to[0], offset=to[1])


def getMultiline(s):
    return '"""' + s + '"""'


def b():
    import pdb;

    pdb.set_trace(sys._getframe().f_back)


def addDocTestToFunc(record, funcdef, indent=True, prompt='>>>'):
    """
>>> add = 'def add(a): return 5'
>>> result = addDocTestToFunc(([3], {}, 5), ast.parse(add).body[0], prompt='-')
>>> print(result)
def add(a):
    ""\"
    - add(3) #@autogenerated
    5
    ""\"
    return 5
>>> print(addDocTestToFunc(([1], {}, 5), ast.parse(result).body[0], prompt='-'))
def add(a):
    ""\"
    - add(3) #@autogenerated
    5
<BLANKLINE>
    - add(1) #@autogenerated
    5
    ""\"
    return 5
    """
    args, kwargs, retv = record
    fdname = funcdef.name

    argsf = ', '.join(str(i) for i in args)
    kwargsf = ', '.join('%s=%s' % (k, v) for k, v in kwargs.items())
    testl = '\n%(prompt)s %(fdname)s(%(argsf)s%(kwargsf)s)' % locals()
    testl = testl + ' #@autogenerated\n%s\n' % retv
    try:
        s = funcdef.body[0].value.s
    except AttributeError:
        s = ''
        funcdef.body = [''] + funcdef.body
    s += testl
    funcdef.body[0] = ast.parse(repr(s)).body[0]
    src = tos(funcdef)
    lines = src.split('\n')
    tab = '    '
    doclines = lines[1].replace("'", '"""').split('\\n')
    if indent:
        doclines = [tab + line.strip() for line in doclines]
    #doclines[0] = doclines[0][4:]
    else:
        doclines[-1] = tab + doclines[-1]

    lines[1] = '\n'.join(doclines)
    return '\n'.join(lines)


def autoadd(a, b):
    """- add(1, 2)
    \t2
    >>> add(1, 1) #@autogenerated
    2
    """
    return a + b


def removeDocTest(funcdef, indent=True, prompt='>>>'):
    """
>>> src = inspect.getsource(autoadd)
>>> removeDocTest(ast.parse(src).body[0])
['- add(1, 2)', '    2']
    """
    doc = ast.get_docstring(funcdef) or None
    lines = doc.split('\n')
    for lineno, line in enumerate(lines):
        if line.endswith('#@autogenerated'):
            del lines[lineno:lineno + 2]
    return lines


def removeAllTests(module, *args, **kwargs):
    """
removeDocTest(ast.parse(autoadd).body[0])
    """
    modlines = open(inspect.getfile(module)).split('\n')
    for obj in module:
        if '__doc__' in dir(obj):
            lines, start = inspect.getsourcelines(obj)
            newsource = removeDocTest('\n'.join(lines))
            modlines[start:start + len(lines) + 1] = newsource
    return modlines


def bp():
    import pydevd

    pydevd.settrace(sys._getframe().f_back)  # @UnresolvedImport


def subdict(keys, dic):
    for key in keys:
        yield key, dic[key]


def add2(a, b):
    """- add2(1, 2)
    2"""
    return a + b


def annotate_functions(callrecords, module):
    """
>>> recorded(add2)(1, 1)
2
>>> lines = annotate_functions({'add2': CallRecords.records['add2']}, sys.modules[__name__])
>>> _, startLines = inspect.getsourcelines(globals()['add2'])
>>> pprint(lines[startLines:startLines+8])
['def add2(a, b):',
 '    ""\"- add2(1, 2)',
 '    ',
 '    2',
 '    >>> add2(1, 1) #@autogenerated',
 '    2',
 '    ""\"',
 '    return a + b']
    """
    lines = open(inspect.getfile(module), 'r').readlines()
    for func, record in callrecords.items():
        #args, kwargs, retv = record
        src, startLines = inspect.getsourcelines(globals()[func])
        #bp()
        funcdef = ast.parse('\n'.join(src)).body[0]
        newsource = addDocTestToFunc(record, funcdef, prompt='>>>')
        lines[startLines:len(src) + startLines + 1] = newsource.split('\n')
    #with file('newfile.py', 'w') as f: f.writelines(lines)
    return lines


class CallRecords:
    log = None

    @staticmethod
    def parseRecords():
        for line in open('record.pydoc', 'r').readlines():
            func_name, args, kwargs, rv = tuple(line.split(' '))
            yield func_name, args, kwargs, rv

    @staticmethod
    def write_cached(func_name, args, kwargs, rv):
        if func_name not in CallRecords.records:
            CallRecords.records[func_name] = (args, kwargs, rv)
            CallRecords.log.write(' '.join([str(i) for i in [func_name, args, kwargs, rv]]))


try:
    CallRecords.records = {f: (args, kw, rv) for f, args, kw, rv in CallRecords.parseRecords()}
except IOError:
    CallRecords.records = {}

CallRecords.log = StringIO()  # ('record.pydoc', 'a')


def recorded(f):
    f.__old__ = f

    @functools.wraps(f)
    def wrapper(*args, **kwargs):
        try:
            return f.f(*args, **kwargs)
        except AttributeError:
            f.f = f
            ret = f(*args, **kwargs)
            f.__call__ = (args, kwargs, ret)
            CallRecords.write_cached(f.__name__, args, kwargs, ret)
            sys.modules[__name__].__dict__[f.__name__] = f
        return ret

    return wrapper


def record_all(func_list, globs=globals()):
    if not hasattr(func_list, '__iter__'):
        func_list = [func_list]

    for f in func_list:
        globs[f.__name__] = recorded(f)


def main():
    globs = {}
    try:
        #doctest.testmod()
        doctest.testmod(raise_on_error=True, globs=globs)
    except doctest.UnexpectedException as failure:
        exc_info = failure.exc_info
        # 		ctx = {}
        # 		for example in failure.test.examples:
        # 			try:
        # 				exec example.source in ctx, globals()
        # 			except Exception, e:
        #
        pm_to.__startframe__ = exc_info[2]
        # TODO: fuzzy?  find functions on the same module that
        # were modified "soon"
        raise exc_info[0](exc_info[1]).with_traceback(exc_info[2])
    except doctest.DocTestFailure as failure:
        example = failure.example
        print(example.source, '?=', example.want, 'got', failure.got, file=sys.stderr)
        try:
            # 			globs = {}
            # 			for ex in failure.test.examples:
            # 				if ex is example: break
            # 				exec ex.source in globs, globals()

            assert eval(example.source, globs, globals()) == eval(example.want, globs, globals())
        except AssertionError:
            pm_to.__frames__ = [tb for tb in inspect.getinnerframes(sys.exc_info()[2])]
            calls = [i for i in ast.walk(ast.parse(failure.example.source)) if
                     isinstance(i, ast.Call)]
            if len(calls) > 0:
                _, fname = calls[-1], calls[-1].func.id
                print('on call ', fname, 'locals are', pm_to(fname), file=sys.stderr)


# TODO: finish debugging the test thang
# WORK on FUNCTION SCAFFOLDING
# Real databse for the CALL RECORDS?

# 		calls = [i for i in ast.walk(ast.parse(failure.example.source)) if isinstance(i, ast.Call)]
# 		for call in calls:
# 			locs = pmed(eval(call.func.id))(*call.args, **(call.kwargs or {}))
# 			import pdb; pdb.set_trace()
# 			print(astor.to_source(call), 'locals()=', locs)


def pm_to(search, startframe=None, module=None, trace=False):
    from pprint import pprint

    with ignored(AttributeError):
        startframe = startframe or pm_to.__startframe__

    try:
        frames = pm_to.__frames__
    except NameError:
        frames = inspect.getinnerframes(startframe)

    frame = [tb[0] for tb in frames
             if search in (tb[3], tb[2])][0]

    for k, v in frame.f_locals.items():
        globals()[k] = v
    if trace:
        pprint(frame.f_locals)
        pdb.set_trace(frame)
    return frame.f_locals


if __name__ == '__main__':
    main()
# bp()
