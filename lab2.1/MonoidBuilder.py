import FSMgenerator
from transitions.extensions import GraphMachine
import itertools
class Regex():
    pass
regex = Regex()
def check_aperiodic(machine, monoid, k, states, regex2):
    #print(monoid.keys())
    machine.set_state(states[0])
    for word in monoid:
        save = monoid[word]
        new = []
        for state in monoid[word]:
            machine.set_state(state)
            for i in range(k-1):
                for char in word:
                    try:
                        regex2.trigger(char)
                        new.append(regex2.state)
                    except:
                        new.append("_")
        if not new == save:
            return False
    return True
def check_cycles(machine, monoid, k, states, regex2):
    machine.set_state(states[0])
    for word in monoid:
        
        save = monoid[word]
        prev = save
        for state in prev:
            machine.set_state(state)
            for i in range(k-1):
                new = []
                for char in word:
                    try:
                        regex2.trigger(char)
                        new.append(regex2.state)
                    except:
                        new.append("_")
                if new == save and not i == 2 and prev==new: 
                    return True
    return False



def main(alphabet, initial_regex, k):

    final_states, states,transitions, initial_regex = FSMgenerator.main(alphabet, initial_regex)
    #print(final_states)
    machine = GraphMachine(model= regex, states=states, transitions=transitions, initial='INPUT')
    regex.get_graph().draw('prefinal.png', prog= 'dot')

    states = list(set(states))

    #print(states)

    regex2 = Regex()
    machine = GraphMachine(model=regex2, states=states, transitions=transitions, initial=initial_regex)
    monoid = {}
    for length in range(1, 20):
        combinations = list(itertools.combinations(alphabet, length))
        for word in combinations:
            monoid[word] = {}
            for state in states:
                machine.set_state(state)
                for char in word:
                    try:
                        regex.trigger(char)
                        monoid[word][state] = regex2.state
                    except:
                        monoid[word][state] = "_"
                
    if check_aperiodic(machine, monoid, k, states, regex2):
        print("Апериодичен")
    else:
        print("Неапериодичен")
    if check_cycles(machine, monoid, k, states, regex2):
        print("Циклы есть")
    else:
        print("Циклов нет")


