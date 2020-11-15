# orusovten-mipt-flat-2020-practice1
***Задача***    
Даны регулярное выражение α и слово u из {a,b,c}*.   
Найти длину самого длинного подслова u в L(α).
***
***Идея алгоритма***   
**Шаг 1** Строим НКА(с возможно epsilon-переходами) по регулярному выражению   
**Шаг 2** Удаляем epsilon-переходы   
**Шаг 3** Переводим НКА в ПДКА   
**Шаг 4** Переводим ПДКА в минимальный ПДКА   
**Шаг 5** "Запускаемся" из стартового состояния по последовательным буквам слева направо, начиная с i-ой, i = 0, 1, ..., |u|.   
На каждой подытерации проверяем, не пришли ли в завершающее состояние, если да, то стараемся обновить ответ.
***
***Оценка асимптотики***   
**Шаг 1** O(|α| * q), где q - число состояний в НКА, в худшем случае для асимптотики все cостояния - завершающие   
**Шаг 2** O(E * q), по каждому символу и по каждому состоянию делаем линейные запуски по eplison-ребрам + ребро-символ.   
**Шаг 3** O((Q * q * E), где Q и q - числа состояний в ПДКА и НКА соответственно, E - число ребер в исходном,   
число итераций равно Q, каждая из них занимает O(q * E), т.к. состояния ПДКА есть "мультисостояния НКА".   
**Шаг 4** O((Q - min_Q) * Q), где Q - число состояний в ПДКА, min_Q - число состояний в МПДКА,   
число итераций(каждая из которых занимает O(Q)) не более, чем (Q - min_Q).   
**Шаг 5** O(|u|^2)   
**Итог** O(|u|^2 + Q * q * E)
