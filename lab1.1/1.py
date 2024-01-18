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

# Примеры использования функции
print(check_structure(['x', 'y', 'x'], ['t', 'v', 't'])) # True
print(check_structure(['x', 'y'], ['t', 't'])) # True
print(check_structure(['x', 'y', 'z'], ['t', 'v', 't'])) # False
print(check_structure(['y', 'y', 'x', 'z', 'x'], ['v', 'v', 'u', 't', 'u'])) # False
