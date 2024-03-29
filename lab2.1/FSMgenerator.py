from transitions import Machine
from transitions.extensions import GraphMachine
import deriv_generator
import functions


class RegularExp():
    pass 
regex = RegularExp()
def main(alphabet, initial_regex):
    final_states, states,transitions,initial_state = getFSM(alphabet, initial_regex)
    
    return (final_states, states,transitions, initial_state)
def getFSM(alphabet, initial_regex):
    tree =deriv_generator.getBinaryTree(deriv_generator.getPostfix(deriv_generator.makeConcat(initial_regex)))
    deriv_generator.postorder(tree)

    tree = functions.makeLeftSided(tree)
    deriv_generator.postorder(tree)
    initial_regex = deriv_generator.inorder(tree)
    #print(initial_regex, 'INITAL')
    final_states = []

    if deriv_generator.lambda_func(tree):
        final_states.append(initial_regex)
    states = [initial_regex]
    
    iterator = 0
    treeStates = []
    transitions = []
    for symbol in alphabet:
        derivative = deriv_generator.getDerived(initial_regex, symbol)
        if deriv_generator.lambda_func(deriv_generator.getBinaryTree(deriv_generator.getPostfix(deriv_generator.makeConcat(derivative)))) and derivative not in final_states:

            final_states.append(derivative)
        while derivative[-1] == ')' and derivative[0] == '(':
            holder = functions.validParentheses(derivative[1:-1])
            if holder:
                derivative = derivative[1:-1]
            else:
                break
        if (not functions.containsSameTree(treeStates, deriv_generator.getBinaryTree(deriv_generator.getPostfix(deriv_generator.makeConcat(derivative)))) in treeStates) and derivative != '∅':
            treeStates.append(deriv_generator.getBinaryTree(deriv_generator.getPostfix(deriv_generator.makeConcat(derivative))))
            states.append(deriv_generator.inorder(deriv_generator.getBinaryTree(deriv_generator.getPostfix(deriv_generator.makeConcat(derivative)))))
        if not derivative == '∅':
            if not {'trigger':symbol, 'source':states[iterator], 'dest': deriv_generator.inorder(deriv_generator.getBinaryTree(deriv_generator.getPostfix(deriv_generator.makeConcat(derivative))))} in transitions:
                transitions.append({'trigger':symbol, 'source':states[iterator], 'dest': deriv_generator.inorder(deriv_generator.getBinaryTree(deriv_generator.getPostfix(deriv_generator.makeConcat(derivative))))})
    iterator +=1
    
    while iterator < len(states):
        if states[iterator] == 'ϵ':
            iterator += 1
            continue
        for symbol in alphabet:
            derivative = deriv_generator.getDerived(states[iterator], symbol)
            
            if deriv_generator.lambda_func(deriv_generator.getBinaryTree(deriv_generator.getPostfix(deriv_generator.makeConcat(derivative)))) and derivative not in final_states:
                final_states.append(derivative)
    
            while derivative[-1] == ')' and derivative[0] == '(':
                holder = functions.validParentheses(derivative[1:-1])
                if holder:
                    derivative = derivative[1:-1]
                else:
                    break
    
            if (not functions.containsSameTree(treeStates, deriv_generator.getBinaryTree(deriv_generator.getPostfix(deriv_generator.makeConcat(derivative)))) in treeStates) and derivative != '∅':
                treeStates.append(deriv_generator.getBinaryTree(deriv_generator.getPostfix(deriv_generator.makeConcat(derivative))))
                #print(derivative)
                states.append(deriv_generator.inorder(deriv_generator.getBinaryTree(deriv_generator.getPostfix(deriv_generator.makeConcat(derivative)))))
            if not derivative == '∅':
                same =functions.containsSameTree(treeStates, deriv_generator.getBinaryTree(deriv_generator.getPostfix(deriv_generator.makeConcat(derivative))))
                if (not {'trigger':symbol, 'source':states[iterator], 'dest': deriv_generator.inorder(deriv_generator.getBinaryTree(deriv_generator.getPostfix(deriv_generator.makeConcat(derivative))))} in transitions):
                    transitions.append({'trigger':symbol, 'source':states[iterator], 'dest': deriv_generator.inorder(same)})
    
    
    
    
                    
            
    
    
        iterator +=1 
    
    
  
    return final_states, states,transitions,initial_regex
if __name__ == "__main__":
    main()
#print(len(treeStates))
