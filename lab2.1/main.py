import MonoidBuilder
if __name__ == "__main__":
    alpha = input('Введите алфавит без точек и запятых (например, abcde): ')
    regex = input('Введите регулярное выражение (например, (a|b)*(abb|ba)): ')
    k = int(input('Введите k: '))
    MonoidBuilder.main(alpha,regex, k)
