import ast

# Функция, которая принимает две строки в виде [x, y, z] и проверяет, 
def check_structure(s1, s2):
  # Проверяем, что длины строк равны
  if len(s1) != len(s2):
    return False
  # Создаем словарь, в котором ключами будут символы из первой строки, 
  # а значениями - соответствующие символы из второй строки
  mapping = {}
  # Проходим по каждому символу из первой строки
  for i in range(len(s1)):
    # Если символ уже есть в словаре, то проверяем, что он соответствует символу из второй строки
    if s1[i] in mapping:
      if mapping[s1[i]] != s2[i]:
        return False
    # Если символа нет в словаре, то добавляем его вместе с символом из второй строки
    else:
      if s2[i] in mapping.values():
        return False
      mapping[s1[i]] = s2[i]
  # Если все проверки прошли успешно, то возвращаем True
  return True

# Функция, которая создает словарь с названием функции и его аргументами
def analyze_function(input_string):
    def analyze_node(node):
        if isinstance(node, ast.Name):
            return [node.id]
        elif isinstance(node, ast.Call):
            function_name = analyze_node(node.func)
            arguments = [analyze_node(arg) for arg in node.args]
            return {'function_name': function_name, 'arguments': arguments}
        elif isinstance(node, ast.BinOp):
            left = analyze_node(node.left)
            right = analyze_node(node.right)
            return {'left': left, 'right': right}
        else:
            return []

    try:
        parsed = ast.parse(input_string, mode='eval')
        result = analyze_node(parsed.body)
        return result
    except SyntaxError as e:
        return f"Error parsing expression: {e}"
    
'''   
parameters_count = {}
recparts = []
funcs = []
variables = []
rul = []
word = []


def checkFun(arr, func):
    for f in arr:
        if f == func:
            return True
    return False
def count_funcs(str):
    #print(str)
    for i in range(len(str) - 1):
        if str[i + 1] == '(' and not checkFun(funcs, str[i]):
            funcs.append(str[i])
        elif str[i] != ')' and (str[i - 1] == '(' or str[i + 1] == ')'):
            variables.append(str[i])
    #print(funcs, variables)

# Создаем словарь, в котором будем хранить количество параметров для каждой функции
def count_parameters(input_string, functions):
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
                    recparts.append(input_string[sr:i+1])
                    process_function(input_string[sr:i+1])
                    sr = -1
                    parameter_count += 1
                    
                elif kk == 0:
                    parameters_count[current_function] = parameter_count

            elif char != ',' and char != ' ' and kk == 1:
                parameter_count += 1         

        return parameters_count

    return process_function(input_string)
'''

# Вывод аргументов всех функций
def extract_arguments(data):


    def flatten_list(lst):
        result = []
        for item in lst:
            if isinstance(item, list):
                result.extend(flatten_list(item))
            else:
                result.append(item)
        return result

    arguments_values = []

    if isinstance(data, dict):
        if 'arguments' in data:
            for i in data['arguments']:
                if isinstance(i, dict):
                    arguments_values.append(extract_arguments(i))
                else:
                    arguments_values.append(i)
       

    return flatten_list(arguments_values)

def check_fun(s11, s22):

    if len(s11) == len(s22):

        k = 0
        for i in range(len(s11)):
            s1 = s11[i]
            s2 = s22[i]
            if not isinstance(s1, dict) and not isinstance(s2, dict):
                k += 1
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
                            return False
                    else:
                        return False
                return False
    return False

def check_args(iter, word, rul):
   for i in range(iter):
        for rule in rul:
            #print(rule[0], '====', word)
            if check_fun([word], [rule[0]]):
                print('ok')
                if check_structure(extract_arguments(word), extract_arguments(rule[0])):
                    print('ok2')
                    return True
            
                    
                    

def main(rules, word, iter):
    rul = []
    for rule in rules:
        ruleLocal = []
        for i in rule:
            ruleLocal.append(analyze_function(i))
        rul.append(ruleLocal)
    word = analyze_function(word)
    #print(word)
    #print(extract_arguments(word))
    check_args(iter, word, rul)
        

    
    
             
             












