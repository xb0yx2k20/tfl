# Лабораторная работа №5 Вариант 2, 4, 5

## Задание

Реализовать Generic LL(1)-разбор слова w по грамматике G с использованием графовидного стека. Входные данные: грамматика G (произвольная КС-грамматика без левой рекурсии), слово w, а также опционально — шаг n разбора, для которого необходимо отрисовать графовидный стек.
Результат работы программы: сообщение об успешном разборе строки с предъявлением (по необходимости) графа разбора на n-ом шаге, либо сообщение о неуспешном разборе с указанием первой найденной ошибочной позиции (то есть такой, в которой невозможен ни один из путей разбора).
n-ый шаг здесь — состояние стека после n действий (действие — применение правила из таблицы), а не
состояние стека после чтения n букв.

## Запуск
Для запуска программы напишите в командной строке команду *python lab5.py 4 '(aa)'* , где первый аргумент это шаг, а второй это аргумент слово