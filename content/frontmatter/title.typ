#import "../main-defs.typ": source, spaced

#let front-page(body) = page(header: none, footer: none, {
  set par(first-line-indent: 0pt, justify: false)
  body
})

// Page 2: the title page of the original, kept by the translation.
#let original-title-page() = front-page[
  #source(2)
  #set text(lang: "en")
  #v(18mm)
  #pad(left: 6mm)[
    #set par(leading: 0.25em)
    #text(size: 17pt)[THEORY\ OF RECURSIVE\ FUNCTIONS\ AND\
      EFFECTIVE\ COMPUTABILITY]
    #v(7mm)
    #text(size: 11pt)[Hartley Rogers, Jr.]
    #v(2mm)
    #text(size: 7.5pt)[Massachusetts Institute of Technology]
    #v(1fr)
    #text(size: 8.5pt)[McGraw-Hill Book Company\
      New York · St. Louis · San Francisco\
      Toronto · London · Sydney]
    #v(6mm)
    #text(size: 10pt)[1967]
    #v(8mm)
  ]
]

// Page 3: the title page of the translation, ranged right.
#let title-page() = front-page[
  #source(3)
  #v(10mm)
  #align(right)[
    #text(size: 11pt)[Х.~~Роджерс]
    #v(9mm)
    #text(font: "Liberation Sans", size: 18pt)[ТЕОРИЯ\ РЕКУРСИВНЫХ\ ФУНКЦИЙ\ И\
      ЭФФЕКТИВНАЯ\ ВЫЧИСЛИМОСТЬ]
    #v(9mm)
    #text(size: 8.5pt)[ПЕРЕВОД С АНГЛИЙСКОГО\
      В.~А.~Душского\
      М.~И.~Кановича\
      Е.~Ю.~Ногиной]
    #v(3mm)
    #text(size: 8.5pt)[ПОД РЕДАКЦИЕЙ\
      В.~А.~Успенского]
  ]
  #v(1fr)
  #align(center, text(size: 9pt)[ИЗДАТЕЛЬСТВО «МИР» МОСКВА 1972])
  #v(8mm)
]

// Page 4: the reverse of the title page, with the annotation and the imprint.
#let imprint-page() = front-page[
  #source(4)
  #set text(size: 8.5pt)
  *УДК 517.11*
  #v(14mm)
  #set par(justify: true, first-line-indent: 1.5em, spacing: 0.44em)
  #pad(x: 9mm)[
    Книга содержит изложение современного состояния теории рекурсивных функций и
    обзор основных приложений этой теории. В~ней прослежено развитие теории
    рекурсивных функций, начиная с ее зарождения в тридцатых годах и кончая
    результатами исследований самых последних лет.

    Не предполагающая в основной своей части никаких предварительных знаний,
    кроме знакомства с теоретико-множественной терминологией, книга Роджерса
    написана хорошим, ясным языком; при этом формальному изложению
    предпосылаются содержательные рассуждения, разъясняющие природу вводимых
    понятий или идей построений и доказательств; в~ней содержится очень много
    упражнений.

    Книга рассчитана на читателей, интересующихся современными проблемами
    математической логики и теории алгоритмов. Она доступна аспирантам и
    студентам старших курсов университетов и пединститутов.
  ]
  #v(1fr)
  #set par(first-line-indent: 0pt, justify: false)
  #set text(size: 7pt)
  #align(center)[
    #text(size: 9pt)[Х.~Роджерс]\
    #text(size: 10pt)[ТЕОРИЯ РЕКУРСИВНЫХ ФУНКЦИЙ И ЭФФЕКТИВНАЯ\ ВЫЧИСЛИМОСТЬ]
    #v(1mm)
    Редакторы _И.~А.~Маховая, Г.~М.~Цуперман._ Художник _Г.~Д.~Коняхина_\
    Художественный редактор _В.~И.~Шаповалов_ Технический редактор
    _Т.~А.~Максимова_\
    Сдано в набор 27/VI 1972~г. Подписано к печати 4/XI 1972~г. Бумага кн.-журн.
    60×90#super[1]/#sub[16]~=~19,5 бум.~л. 39~печ.~л. Уч.-изд.~л. 41,48. Изд.~№
    1/5265. Цена 3~р. 46~к. Зак. 0506\
    #v(1mm)
    ИЗДАТЕЛЬСТВО «МИР», Москва, 1-й Рижский пер., 2\
    Ордена Трудового Красного Знамени Московская типография №~7 «Искра
    революции» «Союзполиграфпрома» при Государственном комитете Совета Министров
    СССР по делам издательств, полиграфии и книжной торговли.\
    г.~Москва, К-1, Трехпрудный пер., 9
  ]
  #v(5mm)
  #align(center, text(size: 8.5pt, style: "italic")[Редакция литературы по
    математическим наукам])
  #v(4mm)
  #text(size: 8pt)[$frac(2 - 2 - 3, 20 - 72)$]
]
