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

# Пример использования:
data = {'function_name': ['f'], 'arguments': [{'function_name': ['h'], 'arguments': [['e'], ['t'], ['r']]}, ['e'],['h'], {'function_name': ['h'], 'arguments': [['e'], ['t'], ['r']]}]}
result = extract_arguments(data)
print(result)
