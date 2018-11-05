#!/usr/bin/env python3
# vim: set expandtab:
import sys
import re
from enum import Enum, auto

EOF = '\0'
EPSILON=''
START_SYMBOL = '<start>'

class Action(Enum):
    Goto = auto()
    Shift = auto()
    Accept = auto()
    Reduce = auto()

RE_NONTERMINAL = re.compile(r'(<[^<> ]*>)')

def split(rule):
    return [s for s in re.split(RE_NONTERMINAL, rule) if s]

def canonical(grammar):
    return  {k: [split(l) for l in rules] for k, rules in grammar.items()}

term_grammar = {'<start>': ['<expr>'],
 '<expr>': ['<term>+<expr>', '<term>-<expr>', '<term>'],
 '<term>': ['<factor>*<term>', '<factor>/<term>', '<factor>'],
 '<factor>': ['+<factor>',
  '-<factor>',
  '(<expr>)',
  '<integer>.<integer>',
  '<integer>'],
 '<integer>': ['<digit><integer>', '<digit>'],
 '<digit>': ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9']}

grammar = canonical(term_grammar)

def rules(g):
    return [(k, e) for k, a in g.items() for e in a]

def terminals(g):
    return set(t for k, expr in rules(g) for t in expr if t not in g)

def symbols(grammar):
    return set(t for k, expr in rules(grammar) for t in expr)

def fixpoint(f):
    def helper(*args):
        while True:
            sargs = repr(args)
            args_ = f(*args)
            if repr(args_) == sargs:
                return args
            args = args_
    return helper

@fixpoint
def nullable_(rules, e):
    for A, expression in rules:
        if all((token in e)  for token in expression): e |= {A}
    return (rules, e)

def nullable(grammar):
    return nullable_(rules(grammar), set())[1]

@fixpoint
def firstset_(rules, first, epsilon):
    for A, expression in rules:
        for token in expression:
            first[A] |= first[token]
            if token not in epsilon: break
    return (rules, first, epsilon)

def firstset(grammar, epsilon):
    first = {i:{i} for i in terminals(grammar)}
    for k in grammar:
        first[k] = {EPSILON} if k in epsilon else set()
    return firstset_(rules(grammar), first, epsilon)[1]

@fixpoint
def followset_(grammar, epsilon, first, follow):
    for A, expression in rules(grammar):
        f_B = follow[A]
        for t in reversed(expression):
            if t in grammar: follow[t] |= f_B
            f_B = f_B | first[t] if t in epsilon else (first[t] - {EPSILON})

    return (grammar, epsilon, first, follow)

def followset(grammar, start):
    follow = {i: set() for i in grammar}
    follow[start] = {EOF}
    epsilon = nullable(grammar)
    first = firstset(grammar, epsilon)
    return followset_(grammar, epsilon, first, follow)

class Parser(object):
    def __init__(self, grammar, start_symbol=START_SYMBOL):
        self.start_symbol = start_symbol
        self.grammar = grammar

    def parse_prefix(self, text):
        """Return pair (cursor, forest) for longest prefix of text"""
        raise NotImplemented()

    def parse(self, text):
        cursor, forest = self.parse_prefix(text)
        if cursor < len(text):
            raise SyntaxError("at " + repr(text[cursor:]))
        return forest

class Item:
    cache = {}
    counter = 0
    def __init__(self, key, expr, dot=0, lookahead=set(), pnum=0):
        self.key,self.expr,self.dot,self.lookahead = key,expr,dot,lookahead
        self.pnum = pnum

    @classmethod
    def init_cache(cls, grammar, fdict):
        for key in sorted(grammar.keys()):
            for expr in grammar[key]:
                Item.cache[str((key, expr, 0))] = Item(key, expr, dot=0, lookahead=fdict[key], pnum=Item.counter)
                Item.counter += 1

    @classmethod
    def get(cls, key, expr, dot):
        val = Item.cache.get(str((key, expr, dot)))
        if val: return val

        seed = Item.cache.get(str((key, expr, 0)))
        val = Item(key, expr, dot, seed.lookahead, seed.pnum)
        Item.cache[str((key, expr, dot))] = val

        return val

    def __repr__(self): return str(self)

    def __str__(self):
        return "[p%s]: %s -> %s \tcursor: %s %s" % (self.pnum,
                self.key, ''.join([str(i) for i in self.expr]), self.dot, '@' + ''.join(sorted(self.lookahead)))

    def advance(self):
        if self.dot >= len(self.expr): return None
        if self.at_dot() == EOF: return None
        return Item.get(self.key, self.expr, self.dot+1)

    def at_dot(self):
        if self.dot >= len(self.expr): return None
        return self.expr[self.dot]

class State:
    counter = 0
    registry = {}
    cache = {}

    def __init__(self, items, grammar):
        self.items = items
        self._tos = {}
        self.i = State.counter
        self.hrow = {}
        self.grammar = grammar
        State.counter += 1
        State.registry[self.i] = self
        self.key = ''.join([str(l) for l in items])
        if self.key in State.cache: raise Exception("Cache already has the state. Use State.get")
        State.cache[self.key] = self

    @classmethod
    def get(cls, items, grammar):
        key = ''.join([str(l) for l in items])
        val = State.cache.get(key)
        if val: return val
        State.cache[key] = State(items, grammar)
        return State.cache[key]

    def __str__(self):
        return "State(%s):\n\t%s" % (self.i, "\n\t".join([str(i) for i in self.items]))

    def __repr__(self): return str(self)

    def construct_initial_state(self, start):
        _, _epsilon, _first, follow = followset(self.grammar, start)
        Item.init_cache(self.grammar, follow)

        pl = Item.get(key=start, expr=self.grammar[start][0], dot=0)
        return  self.form_closure([pl])

    def _to(self, token):
        if token in self._tos: return self._tos[token]
        new_items = []
        for item in self.items:
            if item.at_dot() == token:
                new_item = item.advance()
                if new_item:
                    new_items.append(new_item)
        if not new_items: return None
        s = self.form_closure(new_items)
        self._tos[token] = s
        return s


    def form_closure(self, items):
        return State.get(self.lr1_closure(closure=items, dot=0), self.grammar)

    def lr1_closure(self, closure, dot):
        # get non-terminals following start.dot
        # a) Add the item itself to the closure
        items = closure[:] # copy
        seen = set()
        #for i in items: seen.add(i.key)
        # c) Repeat (b, c) for any new items added under (b).
        while items:
            item, *items = items
            # b) For any item in the closure, A :- α . β γ where the next symbol
            # after the dot is a nonterminal, add the expr rules of that
            # symbol where the dot is before the first item
            # (e.g., for each rule β :- γ, add items: β :- . γ
            token = item.at_dot()
            if not token: continue
            if token in seen: continue
            if token in self.grammar:
                for ps in self.grammar[token]:
                    pl = Item.get(key=token, expr=ps, dot=0)
                    items.append(pl)
                    closure.append(pl)
                    seen.add(pl.key)
        return closure

class LR1Parser(Parser):
    def __init__(self, grammar, start):
        grammar[start][0].append(EOF)
        super().__init__(grammar, start)
        self.construct_states()

    def construct_states(self):
        state1 = State([], self.grammar).construct_initial_state(self.start_symbol)
        states = [state1]
        all_states = set()
        seen = set()
        while states:
            state, *states = states
            if state.i in seen: continue
            seen.add(state.i)
            all_states.add(state)
            sym = symbols(self.grammar)
            for key in sorted(sym): # needs terminal symbols too.
                new_state = state._to(key)
                if new_state:
                    states.append(new_state)
                    action = Action.Shift if key not in self.grammar else Action.Goto
                    state.hrow[key] = (action, new_state.i)

        for state in all_states:
            # for each item, with an LR left of $, add an accept.
            # for each item, with an LR with dot at the end, add a reduce
            # r p
            for line in state.items:
                if line.at_dot() == EOF:
                    state.hrow[EOF] = (Action.Accept, None)
                elif line.dot + 1 > len(line.expr):
                    for key in line.lookahead:
                        state.hrow[key] = (Action.Reduce, line)
        return state1


    def parse(self, input_text):
        expr_stack = []
        state_stack = [State.registry[1].i]
        tokens = list(input_text)
        next_token = None
        tree = []
        while True:
            if not next_token:
                if not tokens:
                    next_token = EOF
                else:
                    next_token, *tokens = tokens
            # use the next_token on the state stack to decide what to do.
            (action, nxt) = State.registry[state_stack[-1]].hrow[next_token]
            if action == Action.Shift:
                next_state = State.registry[nxt]
                # this means we can shift.
                expr_stack.append((next_token, []))
                state_stack.append(next_state.i)
                next_token = None
            elif action == Action.Reduce:
                item = nxt
                # Remove the matched topmost L symbols (and parse trees and
                # associated state numbers) from the parse stack.
                # pop the items' rhs symbols off the stack
                pnum = len(item.expr)
                popped = expr_stack[-pnum:]
                expr_stack = expr_stack[:-pnum]
                # push the lhs symbol of item
                expr_stack.append((item.key, popped))
                # pop the same number of states.
                state_stack = state_stack[:-pnum]
                (action, nxt) = State.registry[state_stack[-1]].hrow[item.key]
                next_state = State.registry[nxt]
                state_stack.append(next_state.i)
            elif action == Action.Goto:
                next_state = State.registry[nxt]
                state_stack.append(next_state.i)
            elif action == Action.Accept:
                break
            else:
                raise Exception("Syntax error")

        assert len(expr_stack) == 1
        return expr_stack[0]

def main(args):
    lr1 = LR1Parser(grammar, START_SYMBOL)
    print(lr1.parse(sys.argv[1]))

if __name__ == '__main__':
    main(sys.argv)
