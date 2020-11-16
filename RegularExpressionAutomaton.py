from collections import deque
from queue import Queue


class MyDFA:
    def __init__(self):
        self.states = set()
        self.input_symbols = set()
        self.transitions = dict()
        self.initial_state = ''
        self.final_states = set()

    def minify(self):
        symbol_classes = dict()
        for state in self.states - self.final_states:
            symbol_classes.update({state: 0})
        for state in self.final_states:
            symbol_classes.update({state: 1})
        equiv_classes = [self.states - self.final_states, self.states]
        alphabet_list = list(self.input_symbols)
        is_end = False
        while not is_end:
            clazzes_dict = dict()
            for state in self.states:
                clazz = (symbol_classes[state],
                         *[symbol_classes[self.transitions[state][symbol]] for symbol in alphabet_list])
                if clazzes_dict.get(clazz) is None:
                    clazzes_dict.update({clazz: {state}})
                else:
                    clazzes_dict[clazz].add(state)
            new_equiv_classes = [set() for i in range(len(clazzes_dict.keys()))]
            new_symbol_classes = dict()
            for i, states in enumerate(clazzes_dict.values()):
                for state in states:
                    new_symbol_classes.update({state: i})
                new_equiv_classes[i] = states
            if len(new_equiv_classes) == len(equiv_classes):
                is_end = True
            equiv_classes = new_equiv_classes
            symbol_classes = new_symbol_classes
        min_dfa = MyDFA()
        min_dfa.input_symbols = self.input_symbols
        for i in range(len(equiv_classes)):
            min_dfa.states.add(i)
            delegate = equiv_classes[i].pop()
            equiv_classes[i].add(delegate)
            for symbol in self.input_symbols:
                if min_dfa.transitions.get(i) is None:
                    min_dfa.transitions.update({i:
                                                    {symbol: symbol_classes[self.transitions[delegate][symbol]]}})
                else:
                    min_dfa.transitions[i].update({symbol:
                                                       symbol_classes[self.transitions[delegate][symbol]]})
            if delegate in self.final_states:
                min_dfa.final_states.add(i)
        min_dfa.initial_state = symbol_classes[self.initial_state]
        return min_dfa


class MyNFA:
    def __init__(self):
        self.states = set()
        self.input_symbols = set()
        self.transitions = dict()
        self.initial_state = 0
        self.final_states = set()

    def bfs(self, start_state, symbol) -> (set, bool):
        queue = Queue()
        queue.put(start_state)
        states = set()
        visited = set()
        is_final = False
        while not queue.empty():
            state = queue.get()
            if state in self.final_states:
                is_final = True
            visited.add(state)
            if self.transitions[state].get(symbol) is not None:
                for neighbour_state in self.transitions[state][symbol]:
                    states.add(neighbour_state)
            if self.transitions[state].get('') is not None:
                for neighbour_state in self.transitions[state]['']:
                    if neighbour_state not in visited:
                        visited.add(neighbour_state)
                        queue.put(neighbour_state)
        return states, is_final

    def deleting_empty_transitions(self):
        new_nfa = MyNFA()
        new_nfa.input_symbols = self.input_symbols - {''}
        new_nfa.initial_state = self.initial_state
        good_states = {self.initial_state}
        while len(good_states) > 0:
            state = good_states.pop()
            new_nfa.transitions.update({state: dict()})
            new_nfa.states.add(state)
            for symbol in new_nfa.input_symbols:
                states, is_final = self.bfs(state, symbol)
                new_nfa.transitions[state].update({symbol: states})
                good_states |= states - new_nfa.states
                if is_final:
                    new_nfa.final_states.add(state)
        return new_nfa

    @staticmethod
    def get_from_set_fields_to_int_fields(states_sets, final_states_sets, set_transitions, alphabet,
                                          initial_state) -> MyDFA:
        my_dfa = MyDFA()
        states_sets_dict = {states_set: i for i, states_set in enumerate(states_sets)}
        my_dfa.initial_state = states_sets_dict.get(frozenset([initial_state]))
        my_dfa.states = set(states_sets_dict.values())
        for set_state in final_states_sets:
            my_dfa.final_states.add(states_sets_dict[set_state])
        my_dfa.transitions = {i: {symbol: states_sets_dict[set_transitions[states_set][symbol]] for symbol in alphabet}
                              for states_set, i in states_sets_dict.items()}
        my_dfa.input_symbols = alphabet
        return my_dfa

    def determinization(self) -> MyDFA:
        states_sets = {frozenset([self.initial_state])}
        final_states_sets = set()
        set_transitions = dict()
        queue = Queue()
        queue.put(frozenset([self.initial_state]))
        while not queue.empty():
            vertices_set = queue.get()
            set_transitions.update({vertices_set: dict()})
            for symbol in self.input_symbols:
                new_vertices_set = set()
                is_terminal = False
                for vertex in vertices_set:
                    if symbol in self.transitions[vertex]:
                        for neighbour_vertex in self.transitions[vertex][symbol]:
                            if neighbour_vertex not in new_vertices_set:
                                new_vertices_set.add(neighbour_vertex)
                                if neighbour_vertex in self.final_states:
                                    is_terminal = True
                new_vertices_set = frozenset(new_vertices_set)
                set_transitions[vertices_set].update({symbol: new_vertices_set})
                if new_vertices_set not in states_sets:
                    states_sets.add(new_vertices_set)
                    queue.put(new_vertices_set)
                    if is_terminal:
                        final_states_sets.add(new_vertices_set)
        return MyNFA.get_from_set_fields_to_int_fields(states_sets, final_states_sets, set_transitions,
                                                       self.input_symbols, self.initial_state)

    number_of_state = 0

    def init_by_symbol(self, symbol):
        if symbol == '1':
            self.initial_state = MyNFA.number_of_state
            MyNFA.number_of_state += 1
            self.transitions = {self.initial_state: {}}
            self.final_states = {self.initial_state}
            self.states = self.final_states
        else:
            new_vertex = MyNFA.number_of_state
            self.initial_state = new_vertex
            MyNFA.number_of_state += 1
            new_vertex = MyNFA.number_of_state
            self.final_states = {new_vertex}
            self.transitions = {self.initial_state: {symbol: {new_vertex}}, new_vertex: {}}
            self.states = {self.initial_state} | self.final_states
            MyNFA.number_of_state += 1
        return self


def sum(left, right) -> MyNFA:  # operator +
    if left.transitions[left.initial_state].get('') is None:
        left.transitions[left.initial_state].update({'': {right.initial_state}})
    else:
        left.transitions[left.initial_state][''].add(right.initial_state)
    left.transitions.update(right.transitions)
    if left.initial_state in left.final_states:
        left.final_states.pop(left.initial_state)
    left.final_states |= right.final_states
    left.states |= right.states
    return left


def concatenate(left, right) -> MyNFA:  # operator .
    for final_state in left.final_states:
        if left.transitions[final_state].get('') is None:
            left.transitions[final_state].update({'': {right.initial_state}})
        else:
            left.transitions[final_state][''].add(right.initial_state)
    left.transitions.update(right.transitions)
    left.states.update(right.states)
    left.final_states = right.final_states
    return left


def star(automaton) -> MyNFA:  # operator *
    for final_state in automaton.final_states:
        automaton.transitions.update({final_state: {'': {automaton.initial_state}}})
    automaton.final_states.add(automaton.initial_state)
    return automaton


def build_automaton(expression, expression_alphabet) -> MyNFA:
    stack = deque()
    for symbol in expression:
        if symbol in expression_alphabet:
            automaton = MyNFA()
            stack.append(automaton.init_by_symbol(symbol))
        elif symbol == "*":
            if len(stack) == 0:
                print("ERROR")
                break
            stack.append(star(stack.pop()))
        elif symbol == "+":
            if len(stack) < 2:
                print("ERROR")
                break
            right = stack.pop()
            left = stack.pop()
            stack.append(sum(left, right))
        elif symbol == ".":
            if len(stack) < 2:
                print("ERROR")
                break
            right = stack.pop()
            left = stack.pop()
            stack.append(concatenate(left, right))
        else:
            print("ERROR")
            break
    if len(stack) != 1:
        print("ERROR")
    else:
        nfa = stack.pop()
        nfa.input_symbols = expression_alphabet - {'1'} | {''}
        return nfa


def count_length_of_the_longest_substring_matching(expression, word) -> int:
    expression_alphabet = {'a', 'b', 'c', '1'}
    my_nfa = build_automaton(expression, expression_alphabet)
    nfa_without_empty_transitions = my_nfa.deleting_empty_transitions()
    dfa = nfa_without_empty_transitions.determinization()
    min_dfa = dfa.minify()
    ans = 0
    for i in range(len(word)):
        pre_ans = 0
        state = min_dfa.initial_state
        for j in range(i, len(word)):
            if word[j] not in min_dfa.input_symbols:
                break
            state = min_dfa.transitions[state][word[j]]
            if state in min_dfa.final_states:
                pre_ans = j - i + 1
        if pre_ans > ans:
            ans = pre_ans
    return ans


if __name__ == '__main__':
    expression = input()
    word = input()
    print(count_length_of_the_longest_substring_matching(expression, word))
