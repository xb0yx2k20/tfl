import sys
import subprocess
import os



funcs = []
variables = []
data = "(set-logic QF_NIA) \n"
allStr = []
parts = []
params = []
recparts = []
message = "(set-logic QF_NIA)\n"
coef_free = []
coefs = []
coefs_in_one = []
mes4 = '(assert (or'
def check_entry(a):
    for s in coefs:
        if a in s:
            return True
    return False

def checkFun(arr, func):
    for f in arr:
        if f == func:
            return True
    return False

#def createData(s):
count = [0] * len(funcs)
                   
       
# f(g(x, h(y)), g(x))
# Заданный массив функций
parameters_count = {}
def count_parameters(input_string, functions):
    # Создаем словарь, в котором будем хранить количество параметров для каждой функции
    
    global parameters_count
    # Функция для обработки вложенных функций
    def process_function(input_string):
        current_function = ""
        inside_function = False
        parameter_count = 0
        i = -1
        sr = -1
        kk = 0
        for char in input_string:
            i += 1
            if char in functions:
                if not inside_function:
                    current_function = char
                    inside_function = True
                else:
                    if sr == -1:
                        sr = i
            elif char == '(' and inside_function:
                kk+=1
            elif char == ')' and inside_function:
                kk-=1
                if kk == 1 and sr!=-1:
                    #print(input_string[sr:i+1], "print")
                    recparts.append(input_string[sr:i+1])
                    process_function(input_string[sr:i+1])
                    sr = -1
                    parameter_count += 1
                    
                elif kk == 0:
                    parameters_count[current_function] = parameter_count

            elif char != ',' and char != ' ' and kk == 1:
                #print(char,"====", current_function)
                parameter_count += 1         

        return parameters_count

    return process_function(input_string)

def create_ner(input_string):
    def process_function(input_string):
        current_function = ""
        inside_function = False
        parameter_count = 0
        i = -1
        sr = -1
        kk = 0
        ner = ""
        for char in input_string:
            i += 1
            if char in funcs:
                if not inside_function:
                    current_function = char
                    inside_function = True
                    parameter_count = parameters_count[current_function]
                    ner += char + "0"
                    parameter_count -= 1
                else:
                    if sr == -1:
                        sr = i
            elif char == '(' and inside_function:
                kk+=1
            elif char == ')' and inside_function:
                kk-=1
                if kk == 1 and sr!=-1:
                    recparts.append(input_string[sr:i+1])
                    ner += f"*({process_function(input_string[sr:i+1])}) + {current_function}{parameters_count[current_function] - parameter_count}"
                    parameter_count -= 1
                    sr = -1
                    
                elif kk == 0:
                    return ner

            elif kk == 1 and char in variables:
                #print(char,"====", current_function)
                ner +=  f"*{char} + {current_function}{parameters_count[current_function] - parameter_count}"
                parameter_count -= 1

        return ner

    return process_function(input_string)

def get_coef(var, s):
    global message, coef_free
    res = ''
    stack = []
    if var not in s and var != ')':
        return '0'
    for i in range(len(s)):
        if s[i] == '(':
            stack.append(i)
        if s[i] == ')':
            if s[i] == var:
                res += s[i-2:i] + '*'
                if s[i-2:i] not in coef_free:
                    coef_free.append(s[i-2:i])
                for i in range(len(stack) - 1, -1, -1):
                    res += s[stack[i] - 3:stack[i]]
            res += "  "
            stack.pop()
        if s[i] == var:
            res += s[i-3:i]
            for i in range(len(stack) - 1, -1, -1):
                res += s[stack[i] - 3:stack[i]]
            res += "  "
    if var == ')':
        x = s[-2] + s[-1]
        res += x
        if x not in coef_free:
            coef_free.append(x)
    parts = res.split(" ")

    for part in parts:
        x = part.split('*')
        
    return res

def create_mes1(res, res2): 
    global message, mes4
    res = res.split(' ')
    mas = []
    for i in res:
        if i != '':
            mas.append(i)
    #print(mas, "mas")
    res2 = res2.split(' ')
    mas2 = []
    for i in res2:
        if i != '':
            mas2.append(i)

    Mas = []
    Mas.append(mas)
    Mas.append(mas2)
    #print(Mas, "Mrs")

    message1 = '(assert (>='

    for mas in Mas:
        if len(mas) > 1:
            message1 += " (+"
            for i in mas:
                i = [x for x in filter(lambda i: i != '', i.split('*'))]
                #print(i, "i")
                if len(i) > 1:
                    message1 += " (*"

                    for j in i:
                        message1 += ' ' + j
                    message1 += ')'
                if len(i) == 1:
                    message1 += ' ' + i[0]
            message1 += ')'
        elif len(mas) == 1:
            pers = [x for x in filter(lambda i: i != '', mas[0].split('*'))]
            if len(pers) > 1:
                message1 += " (*"
                for per in pers:
                    message1 += ' ' + per
                message1 += ')'
            elif len(pers) == 1:
                message1 += ' ' + pers[0]
            
            
            #print([x for x in filter(lambda i: i != '', mas[0].split('*'))], "message")
    message1 += '))'   
    message += message1 + '\n'
    return message1
            



    #(assert (>= (* a2 a0) a2))
    
def create_mes2():
    global message, coefs_in_one
    message += "(assert (and"
    for i in range(len(coefs_in_one)):
        x = 1
        if coefs_in_one[i] in coef_free:
            x = 0
        message += f" (>= {coefs_in_one[i]} {x})"
    message += "))"
    
def create_mes3(mas):
    res = "(assert (or"
    if len(mas) >= 1:
        res += " (and"
        for i in range(len(mas) - 1):
            mas[i] = mas[i][:-1].replace("(assert ", '')
            mas[i] = mas[i].replace("=", '')
            res += " " + mas[i]
        res += ")"
    mas[-1] = mas[-1][:-1].replace("(assert ", '')
    mas[-1] = mas[-1].replace("=", '')
    res += " " + mas[-1] + "))\n"
    '''print(mas)
    print(res)'''
    return res

def create_mes4():
    global parameters_count
    ms = '(assert (and'
    for i in parameters_count:
        ms += " (or"
        if (parameters_count[i]) == 2:
            ms += " (and"
            for j in range(2):
                ms += f' (> {i}{j} 1)'
            ms += ")"
            ms += f' (> {i}{2} 0)'
        if (parameters_count[i]) == 1:
            ms += f' (> {i}{0} 1)' + f' (> {i}{1} 0)'
        ms += ')'
    ms += '))'
    return ms
        

def main():
    global parameters_count, message, coefs, coefs_in_one, mes4

    """str = ""
    for line in sys.stdin:
        if len(line) == 1:
            break
        str += line

    str = str[:len(str) - 1]"""
    #print(str)
    lines = ''
    with open("lab1/input.txt", "r") as file:
        str = file.readline()

    
        for i in range(len(str) - 1):
            if str[i + 1] == '(' and not checkFun(funcs, str[i]):
                funcs.append(str[i])
            elif str[i] != ')' and (str[i - 1] == '(' or str[i + 1] == ')') and not checkFun(variables, str[i]) and not checkFun(funcs, str[i]):
                variables.append(str[i])
        parameters_count = {func: 0 for func in funcs}

        oneStr = ""
        for s in str:
            if s == '\n':
                allStr.append(oneStr)
                oneStr = ""
            oneStr += s
        allStr.append(oneStr)


        
        for s in allStr:
            parts.append(s.split(" -> "))
        parameters1 = count_parameters(parts[0][0], funcs)
        parameters2 = count_parameters(parts[0][1], funcs)
        for func, count in parameters2.items():
            print(f"Функция {func} имеет {count} параметров.")
        for func, count in parameters2.items():
            str = []
            if count == 0:
                for i in range(2):
                    str.append(f"{func}{i}")
                coefs.append(str)
            else:
                for i in range(count + 1):
                    str.append(f"{func}{i}")
                coefs.append(str)
        for i in range(len(funcs)):
            print(funcs[i], coefs[i])
            for x in coefs[i]:
                message += f'(declare-fun {x} () Int)\n'
                coefs_in_one.append(x)
        message +='\n'
        

        res1 = create_ner(parts[0][0])
        res2 = create_ner(parts[0][1])
        

        qwe = []
        for i in range(len(variables)):
            if variables[i] != '(':
                qwe.append(create_mes1(get_coef(variables[i], res1), get_coef(variables[i], res2)))
        qwe.append(create_mes1(get_coef(")", res1), get_coef(")", res2)))
        message += '\n'

        create_mes2()
    #f(g(x, h()) -> f(x)

        


        message += '\n' + create_mes3(qwe) + '\n'

        message += create_mes4() + '\n' + '\n'

        message += "(check-sat)\n(get-model)\n(exit) final"

        #print(message)

                    
        
        


        f = open("lab1.smt2", "w")

        f.write(message)
        f.close()

        proc = subprocess.Popen("z3 -smt2 lab1.smt2", stdout=subprocess.PIPE, shell=True)
        (out, err) = proc.communicate()

        result = out.decode()
        with open("lab1/output.txt", "w") as f:
            f.write(result)
        print("\n", result)

        os.remove("lab1.smt2")



if __name__ == '__main__':
    print('Пример ввода: f(g(x, y)) -> g(x, y)')
main()


