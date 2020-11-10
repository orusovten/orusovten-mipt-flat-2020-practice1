from collections import deque
from queue import Queue


class MyDFA:
    split_symbol = ":"

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
        equiv_classes = [self.states - self.final_states, self.final_states.copy()]
        alphabet_list = list(self.input_symbols)
        is_end = False
        while not is_end:
            common_separator_dict = dict()
            state_separator = dict()
            for state in self.states:
                separator = ""
                for symbol in alphabet_list:
                    separator += str(symbol_classes[self.transitions[state][symbol]]) + MyDFA.split_symbol
                if common_separator_dict.get(separator) is None:
                    common_separator_dict.update({separator: {state}})
                else:
                    common_separator_dict[separator].add(state)
                state_separator.update({state: separator})
            new_symbol_classes = dict()
            new_equiv_classes = list()
            is_end = True
            for equiv_class in equiv_classes:
                count_iterations = 0
                while len(equiv_class) > 0:
                    first_state = equiv_class.pop()
                    separator = state_separator[first_state]
                    equiv_class.add(first_state)
                    for state in equiv_class & common_separator_dict[separator]:
                        new_symbol_classes.update({state: len(new_equiv_classes)})
                    new_equiv_classes.append(equiv_class & common_separator_dict[separator])
                    count_iterations += 1
                    equiv_class -= common_separator_dict[separator]
                if count_iterations > 1:
                    is_end = False
            symbol_classes = new_symbol_classes
            equiv_classes = new_equiv_classes
        min_dfa = MyDFA()
        min_dfa.input_symbols = self.input_symbols
        for i in range(len(equiv_classes)):
            min_dfa.states.add(str(i))
            delegate = equiv_classes[i].pop()
            equiv_classes[i].add(delegate)
            for symbol in self.input_symbols:
                if min_dfa.transitions.get(str(i)) is None:
                    min_dfa.transitions.update({str(i):
                                                {symbol: str(symbol_classes[self.transitions[delegate][symbol]])}})
                else:
                    min_dfa.transitions[str(i)].update({symbol:
                                                        str(symbol_classes[self.transitions[delegate][symbol]])})
            if delegate in self.final_states:
                min_dfa.final_states.add(str(i))
        min_dfa.initial_state = symbol_classes[self.initial_state]
        return min_dfa


class MyNFA:
    split_symbol = ":"
    def __init__(self):
        self.states = set()
        self.input_symbols = set()
        self.transitions = dict()
        self.initial_state = ""
        self.final_states = set()

    def invert(self):
        invert_nfa = MyNFA()
        invert_nfa.initial_state = self.initial_state
        invert_nfa.final_states = self.final_states
        invert_nfa.input_symbols = self.input_symbols
        invert_nfa.states = self.states
        for state in self.states:
            invert_nfa.transitions.update({state: dict()})
        for state in self.states:
            for symbol in self.input_symbols:
                if self.transitions[state].get(symbol) is not None:
                    for neigh_state in self.transitions[state][symbol]:
                        if invert_nfa.transitions[neigh_state].get(symbol) is None:
                            invert_nfa.transitions[neigh_state].update({symbol: {state}})
                        else:
                            invert_nfa.transitions[neigh_state][symbol].add(state)
        return invert_nfa

    def deleting_empty_transitions(self):
        new_nfa = MyNFA()
        new_nfa.states = self.states
        new_nfa.input_symbols = self.input_symbols - {''}
        new_nfa.initial_state = self.initial_state
        for state in self.states:
            new_nfa.transitions.update({state: dict()})
            for symbol in new_nfa.input_symbols:
                current_states = {state}  # вершины, при проходе к которым только куча epsilon
                del_current_states = set()  # помогает избежать проблем с epsilon-зацикливанием
                waiting_states = set()  # вершины, при проходе к которым куча epsilon и один symbol
                while len(current_states) > 0:
                    current_state = current_states.pop()
                    del_current_states.add(current_state)
                    if self.transitions[current_state].get('') is not None:
                        current_states |= self.transitions[current_state][''] - del_current_states
                    if self.transitions[current_state].get(symbol) is not None:
                        for neigh_state in self.transitions[current_state][symbol]:
                            waiting_states.add(neigh_state)
                del_waiting_states = set()  # помогает избежать проблем с epsilon-зацикливанием
                while len(waiting_states) > 0:
                    waiting_state = waiting_states.pop()
                    if new_nfa.transitions[state].get(symbol) is None:
                        new_nfa.transitions[state].update({symbol: {waiting_state}})
                    else:
                        new_nfa.transitions[state][symbol].add(waiting_state)
                    del_waiting_states.add(waiting_state)
                    if self.transitions[waiting_state].get('') is not None:
                        waiting_states |= self.transitions[waiting_state][''] - del_waiting_states
        invert_nfa = self.invert()
        new_final_states = self.final_states
        del_new_final_states = set()
        while len(new_final_states) > 0:
            final_state = new_final_states.pop()
            del_new_final_states.add(final_state)
            new_nfa.final_states.add(final_state)
            if invert_nfa.transitions[final_state].get('') is not None:
                new_final_states |= invert_nfa.transitions[final_state][''] - del_new_final_states
        return new_nfa

    def determinization(self) -> MyDFA:
        my_dfa = MyDFA()
        my_dfa.initial_state = self.initial_state
        my_dfa.states = {self.initial_state}
        my_dfa.input_symbols = self.input_symbols
        queue = Queue()
        queue.put(self.initial_state)
        while not queue.empty():
            tops = queue.get()
            tops_list = tops.split(MyNFA.split_symbol)
            tops_list.pop()
            my_dfa.transitions[tops] = dict()
            for symbol in self.input_symbols:
                new_set_vertex = set()
                is_terminal = False
                for top in tops_list:
                    top += MyNFA.split_symbol
                    if symbol in self.transitions[top]:
                        for vertex in self.transitions[top][symbol]:
                            if vertex not in new_set_vertex:
                                new_set_vertex.add(vertex)
                                if vertex in self.final_states:
                                    is_terminal = True
                new_vertex = ""
                for vertex in sorted(list(new_set_vertex)):
                    new_vertex += vertex
                my_dfa.transitions[tops][symbol] = new_vertex
                if new_vertex not in my_dfa.states:
                    my_dfa.states.add(new_vertex)
                    queue.put(new_vertex)
                    if is_terminal:
                        my_dfa.final_states.add(new_vertex)
        return my_dfa


class Result:
    split_symbol = ":"
    number_of_state = 0

    def __init__(self, symbol):
        if symbol == '1':
            self.initial_state = str(Result.number_of_state) + Result.split_symbol
            Result.number_of_state += 1
            self.transitions = {self.initial_state: {}}
            self.final_states = {self.initial_state}
            self.states = self.final_states
        else:
            new_vertex = str(Result.number_of_state) + Result.split_symbol
            self.initial_state = new_vertex
            Result.number_of_state += 1
            new_vertex = str(Result.number_of_state) + Result.split_symbol
            self.final_states = {new_vertex}
            self.transitions = {self.initial_state: {symbol: {new_vertex}}, new_vertex: {}}
            self.states = {self.initial_state} | self.final_states
            Result.number_of_state += 1


def combine(left, right) -> Result:  # operator +
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


def glue(left, right) -> Result:  # operator .
    for final_state in left.final_states:
        if left.transitions[final_state].get('') is None:
            left.transitions[final_state].update({'': {right.initial_state}})
        else:
            left.transitions[final_state][''].add(right.initial_state)
    left.transitions.update(right.transitions)
    left.states.update(right.states)
    left.final_states = right.final_states
    return left


def star(result) -> Result:  # operator *
    for final_state in result.final_states:
        result.transitions.update({final_state: {'': {result.initial_state}}})
    result.final_states.add(result.initial_state)
    return result


def build_automata(expression, expression_alphabet) -> MyNFA:
    stack = deque()
    for symbol in expression:
        if symbol in expression_alphabet:
            stack.append(Result(symbol))
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
            stack.append(combine(left, right))
        elif symbol == ".":
            if len(stack) < 2:
                print("ERROR")
                break
            right = stack.pop()
            left = stack.pop()
            stack.append(glue(left, right))
        else:
            print("ERROR")
            break
    if len(stack) != 1:
        print("ERROR")
    else:
        result = stack.pop()
        alphabet = (expression_alphabet - {'1'}) | {''}
        nfa = MyNFA()
        nfa.initial_state = result.initial_state
        nfa.input_symbols = alphabet
        nfa.transitions = result.transitions
        nfa.final_states = result.final_states
        nfa.states = result.states
        return nfa


def count_length_of_the_longest_substring_in_regular_expression_language(expression, word) -> int:
    expression_alphabet = {'a', 'b', 'c', '1'}
    my_nfa = build_automata(expression, expression_alphabet)
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
            state = min_dfa.transitions[str(state)][word[j]]
            if state in min_dfa.final_states:
                pre_ans = j - i + 1
        if pre_ans > ans:
            ans = pre_ans
    return ans


if __name__ == '__main__':
    expression = input()
    word = input()
    print(count_length_of_the_longest_substring_in_regular_expression_language(expression, word))


