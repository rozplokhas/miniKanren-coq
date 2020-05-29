# miniKanren-coq

Сертифицированная семантика языка miniKanren, версия для магистерской дипломной работы.

Для сборки и проверки всех доказательств используйте команду `make`.

В папке 'src' находится формализация системы и всех доказательств.

- Unify.v -- используемые понятия из теории унификации (термы, подстановки, вычисление наиболее общего унификатора)
- Stream.v -- потенциально бесконечные потоки и их свойства
- MiniKanrenSyntax.v -- синтаксис базового языка (аксиома 'Prog' здесь фиксирует произвольную корректную программу)
- DenotationalSem.v -- денотационная семантика
- OperationalSem.v -- операционная семантика для поиска с чередованием
- OpSemSoundness.v -- корректность операционной семантики относительно денотационной
- OpSemCompleteness.v -- полнота операционной семантики относительно денотационной


В папке 'extracted' находится извлеченный корректный по построению интерпретатор:

- interpreter.hs -- код извлеченный из операционной семантики для поиска с чередованием (из файла OperationalSem.v)
- interpreter_wrapped.hs -- код из файла interpreter.hs, к которому дописаны вспомогательные примитивы для более удобной презентации и использования и несколько тестов
