#!/usr/bin/env python3
# vim: set expandtab:
import sys
import json
import re
import collections
import logging as log
log.basicConfig( stream=sys.stdout, level=log.DEBUG )

EOF = '\0'
EPSILON=''
START_SYMBOL = '<start>'

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

def et(v):
    return v.replace("\t", " ").replace("\n", " ")

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

class PLine:
    cache = {}
    counter = 0
    fdict = None
    def __init__(self, key, production, cursor=0, lookahead=set(), pnum=0):
        self.key,self.production,self.cursor,self.lookahead = key,production,cursor,lookahead
        self.tokens = self.production
        self.pnum = pnum

    @classmethod
    def reset(cls):
        PLine.cache.clear()
        PLine.fdict = None
        PLine.counter = 0

    @classmethod
    def init_cache(cls, grammar, fdict):
        PLine.fdict = fdict
        for key in sorted(grammar.keys()):
            for production in grammar[key]:
                PLine.cache[str((key, production, 0))] = PLine(key, production,
                        cursor=0, lookahead=fdict[key], pnum=PLine.counter)
                PLine.counter += 1
        return len(PLine.cache.keys())

    @classmethod
    def get(cls, key, production, cursor):
        """
        Try to get a predefined pline. If we fail, create new instead.
        """
        val = PLine.cache.get(str((key, production, cursor)))
        if val: return val

        seed = PLine.cache.get(str((key, production, 0)))
        val = PLine(key, production, cursor, seed.lookahead, seed.pnum)
        PLine.cache[str((key, production, cursor))] = val

        return val

    @classmethod
    def from_seed(cls, obj, cursor):
        """
        To be used when we need a new pline when we advance the current pline.
        Important: the production rule is unchanged. Only the cursor may be
        different
        """
        return PLine.get(obj.key, obj.production, cursor)

    def production_number(self):
        """
        The number of the original production rule.
        Does not consider cursor location
        """
        return self.pnum

    def __repr__(self): return str(self)

    def __str__(self):
        return "[p%s]: %s -> %s \tcursor: %s %s" % (self.production_number(),
                self.key, ''.join([str(i) for i in self.tokens]), self.cursor, '@' + ''.join(sorted(self.lookahead)))

    def advance(self):
        if self.cursor >= len(self.tokens): return '', None
        if self.at(self.cursor) == EOF: return '', None
        token = self.at(self.cursor)
        return token, PLine.from_seed(self, self.cursor+1)

    def at(self, cursor):
        if cursor >= len(self.tokens): return None
        return self.tokens[cursor]

def lr1_closure(closure, cursor, grammar):
    # get non-terminals following start.cursor
    # a) Add the item itself to the closure
    items = closure[:] # copy
    seen = set()
    #for i in items: seen.add(i.key)
    # c) Repeat (b, c) for any new items added under (b).
    while items:
        item, *items = items
        # b) For any item in the closure, A :- α . β γ where the next symbol
        # after the dot is a nonterminal, add the production rules of that
        # symbol where the dot is before the first item
        # (e.g., for each rule β :- γ, add items: β :- . γ
        token = item.at(item.cursor)
        if not token: continue
        if token in seen: continue
        if token in grammar:
            for ps in grammar[token]:
                pl = PLine.get(key=token, production=ps, cursor=0)
                items.append(pl)
                closure.append(pl)
                seen.add(pl.key)
    return closure

class State:
    counter = 1
    registry = {}
    cache = {}
    def reset():
        PLine.reset()
        State.counter = 1
        State.registry = {}
        State.cache = {}

    def __init__(self, plines, sfrom=None):
        self.plines = plines
        self.shifts = {}
        self.go_tos = {}
        self.i = State.counter
        self.row = []
        self.hrow = {}
        self.note = "*"
        if sfrom:
            self.grammar = sfrom.grammar
            self.start = sfrom.start
        State.counter += 1
        State.registry[self.i] = self
        self.key = ''.join([str(l) for l in plines])
        if State.cache.get(self.key): raise Exception("Cache already has the state. Use State.get")
        State.cache[self.key] = self

    @classmethod
    def get(cls, plines, sfrom=None):
        key = ''.join([str(l) for l in plines])
        val = State.cache.get(key)
        if val: return val
        State.cache[key] = State(plines, sfrom)
        return State.cache[key]

    def __str__(self):
        return "State(%s):\n\t%s" % (self.i, "\n\t".join([str(i) for i in self.plines]))

    def __repr__(self): return str(self)

    @classmethod
    def construct_initial_state(cls, grammar, start=START_SYMBOL):
        _, _epsilon, _first, follow = followset(grammar, start)
        PLine.init_cache(grammar, follow)
        production_str = grammar[start][0]

        pl = PLine.get(key=start, production=production_str, cursor=0)

        lr1_items = lr1_closure(closure=[pl], cursor=0, grammar=grammar)
        state =  cls(lr1_items, 0)
        # seed state
        state.start, state.grammar = start, grammar
        return state

    def go_to(self, token):
        if self.go_tos.get(token): return self.go_tos[token]
        if token not in self.grammar: return None
        new_plines = []
        for pline in self.plines:
            tadv, new_pline = pline.advance()
            if token == tadv:
                new_plines.append(new_pline)
        if not new_plines: return None
        s = self.form_closure(new_plines)
        self.go_tos[token] = s
        s.note = "%s -> [%s] -> " % (self.i,  token)
        return s

    def shift_to(self, token):
        if self.shifts.get(token): return self.shifts[token]
        if token in self.grammar: return None
        new_plines = []
        for pline in self.plines:
            tadv, new_pline = pline.advance()
            if token == tadv:
                new_plines.append(new_pline)
        if not new_plines: return None
        # each time we shift, we have to build a new closure, with cursor at 0
        # for the newly added rules.
        s = self.form_closure(new_plines)
        self.shifts[token] = s
        s.note = "%s -> [%s] -> " % (self.i,  token)
        return s

    def form_closure(self, plines):
        closure = lr1_closure(closure=plines, cursor=0, grammar=self.grammar)
        s = State.get(plines=plines, sfrom=self)
        return s

    def get_reduction(self, nxt_tok):
        # is the cursor at the end in any of the plines?
        for pline in self.plines:
            if pline.cursor + 1 >= len(pline.tokens):
                res = nxt_tok in pline.lookahead
                if res: return pline
        # return the production number too for this pline
        return None

    @classmethod
    def construct_states(cls, grammar, start=START_SYMBOL):
        state1 = State.construct_initial_state(grammar, start)
        states = [state1]
        follow = {}
        all_states = set()
        seen = set()
        while states:
            state, *states = states
            if state.i in seen: continue
            seen.add(state.i)
            all_states.add(state)
            sym = symbols(grammar)
            for key in sorted(sym): # needs terminal symbols too.
                if key not in grammar:
                    new_state = state.shift_to(key)
                    if new_state: # and new_state.i not in seen:
                        states.append(new_state)
                        state.hrow[key] = ('Shift', new_state.i)
                    else:
                        state.hrow[key] = ('_', None)
                else:
                    new_state = state.go_to(key)
                    if new_state: # and new_state.i not in seen:
                        states.append(new_state)
                        state.hrow[key] = ('Goto', new_state.i)
                    else:
                        state.hrow[key] = ('_', None)

        for state in all_states:
            # for each item, with an LR left of $, add an accept.
            # for each item, with an LR with dot at the end, add a reduce
            # r p
            for line in state.plines:
                if line.at(line.cursor) == EOF:
                    key = EOF 
                    state.hrow[key] = ('Accept', None)
                elif line.cursor + 1 > len(line.tokens):
                    for key in line.lookahead:
                        state.hrow[key] = ('Reduce', line)
        return state1

def parse(input_text, grammar):
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
        if action == 'Shift':
            next_state = State.registry[nxt]
            # this means we can shift.
            expr_stack.append(next_token)
            state_stack.append(next_state.i)
            next_token = None
        elif action == 'Reduce':
            pline = nxt
            # Remove the matched topmost L symbols (and parse trees and
            # associated state numbers) from the parse stack.
            # pop the plines' rhs symbols off the stack
            pnum = len(pline.tokens)
            popped = expr_stack[-pnum:]
            expr_stack = expr_stack[:-pnum]
            # push the lhs symbol of pline
            expr_stack.append({pline.key: popped})
            # pop the same number of states.
            state_stack = state_stack[:-pnum]
            (action, nxt) = State.registry[state_stack[-1]].hrow[pline.key]
            next_state = State.registry[nxt]
            state_stack.append(next_state.i)
        elif action == 'Goto':
            next_state = State.registry[nxt]
            state_stack.append(next_state.i)
        elif action == 'Accept':
            break
        else:
            raise Exception("Syntax error")

    assert len(expr_stack) == 1
    return expr_stack[0]

def initialize(grammar, start):
    grammar[start][0].append(EOF)
    State.construct_states(grammar, start)

def main(args):
    initialize(grammar, START_SYMBOL)
    val = parse(sys.argv[1], grammar)
    print(json.dumps(val))

if __name__ == '__main__':
    main(sys.argv)
