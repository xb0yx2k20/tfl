

def check_fun(s11, s22):

    if len(s11) == len(s22):

        k = 0
        for i in range(len(s11)):
            s1 = s11[i]
            s2 = s22[i]
            print(s11, '===', s22)
            if not isinstance(s1, dict) and not isinstance(s2, dict):
                k += 1
            print(k, 'k')
            print(len(s11), 'ln')
            if k == len(s11):
                return True

        for i in range(len(s11)):
            s1 = s11[i]
            s2 = s22[i]
            
            if len(s1) != 1 and len(s2) != 1:

                if s1['function_name'] == s2['function_name']:
                    
                    if len(s1["arguments"]) == len(s2["arguments"]):
                        if (check_fun(s1["arguments"], s2["arguments"])) == True:
                            return True
                        else:
                            print(1)
                            return False
                    else:
                        print(2)
                        return False
                print(3)
                return False

    print(5)
    return False

print(check_fun([{'function_name': ['f'], 'arguments': [['x'], {'function_name': ['h'], 'arguments': [['y']]}]}], [{'function_name': ['f'], 'arguments': [['e'], {'function_name': ['h'], 'arguments': [['t']]}]}]))
#print(delete_scobs({'function_name': ['h'], 'arguments': [['e'], ['t']]}))
print(check_fun([['e'], ['t'], ['t']], [['e'], ['t'], ['t']]))