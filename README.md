# QED-Seminar 2024

## Editoren

### Web-Editor

Zum Bearbeiten/Auswerten einer einzelnen Datei ist oftmals der Web-Editor ausreichend.  Es gibt zwei Server mit im wesentlichen identischen Editoren:

- https://lean.math.hhu.de/
- https://live.lean-lang.org/

Kurze Dateien lassen sich einfach durch Kopieren und Versenden der URL teilen. Längere Dateien kann man herauf- und herunterladen.

### Lokale Installation

Um an Projekten zu arbeiten, die aus mehreren Dateien bestehen, kommt man meist an einer lokalen Installation von Lean nicht herum.  Der Editor mit der besten Unterstützung für die Entwicklung in Lean ist VS Code.  Auf der Leanprover-Community-Seite gibt es für Lean und VS Code eine [Installationsanleitung](https://leanprover-community.github.io/get_started.html). 
Nach erfolgreicher Installation ist der nächste Schritt, ein [Projekt zu initialisieren](https://leanprover-community.github.io/install/project.html), z.B. durch Klonen dieses Repositories.

## Hilfe

### Lehrbuch

[Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/) führt systematisch in die Syntax von Lean ein und behandelt wichtige Teile der Beweisbibliothek mathlib. Kapitel 6 (*Structures*) und 7 (*Hierarchies*) gehen bereits deutlich über das hinaus, was im Robo-Spiel vorkommt.  Wer sich für Algebra interessiert, liest dann in Kaptitel 8 (*Groups and Rings*) weiter, wer sich eher für Analysis interessiert, in Kapitel 9 (*Topology*). 

### Taktiken

- [Floris van Doorn's Cheat Sheet](https://github.com/fpvandoorn/LeanCourse23/blob/master/lean-tactics.pdf) 
- [Martin Dvorak's Cheat Sheet](https://github.com/madvorak/lean4-tactics)

Die Taktik-Varianten mit Fragezeichen (`simp?`, `exact?`, `apply?`, `rw?`) kamen im Spiel nicht vor, sind aber sehr nützlich – einfach mal ausprobieren!  Auch `aesop?` kann Beweise abkürzen.

### mathlib-Dokumentation

In der [offiziellen Dokumentation von mathlib](https://leanprover-community.github.io/mathlib4_docs/) gibt es eine rudimentäre Suchfunktion.  Wenn man keine Idee hat, wie der Satz heißen könnte, nach dem man sucht, benutzt man besser [Loogle](https://loogle.lean-lang.org/). Um zum Beispiel den Satz

    theorem imp_iff_not_or : A → B ↔ ¬A ∨ B

in `mathlib` zu finden, würde man `(_ → _ ) ↔ (¬ _ ∨ _)` looglen.
Loogle versteht `->` und `<->` anstelle von `→` und `↔`.  Um Suchanfragen mit anderen Unicode-Symbolen zu formulieren, muss man die Anfrage zunächst in einem externen Editor formulieren und nach Loogle kopieren.

### Zulip

Es gibt eine sehr freundliche weltweite [Lean/mathlib-Community](https://leanprover.zulipchat.com/), die rund um die Uhr Fragen beantwortet.  Um Fragen zu stellen, muss man sich allerdings zunächst einen Account auf Zulip zulegen.  Die erste Anlaufstelle ist dann der [`new members`-Kanal](https://leanprover.zulipchat.com/#narrow/stream/113489-new-members).


## Los geht's …

Wir wollen uns im zweiten Teil des Seminars elementarer Analysis zuwenden.  Um die Formulierung von Analysis in mathlib nachvollziehen zu können, benötigen wir das das Konzept eines *Filters*.  Dazu:

- das Topologie-Kapitel in [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/C09_Topology.html)
- ein [hilfreiches Bild](https://commons.wikimedia.org/wiki/File:Filter_vs_ultrafilter.svg) auf Wikipedia
- ein [kleines Tutorium](https://github.com/hhu-adam/QEDSeminar2024/blob/main/QEDSeminar2024/Tutorial_Filters.lean) in diesem repository ([Web-Editor](https://lean.math.hhu.de/#url=https%3A%2F%2Fraw.githubusercontent.com%2Fhhu-adam%2FQEDSeminar2024%2Fmain%2FQEDSeminar2024%2FTutorial_Filters.lean))
