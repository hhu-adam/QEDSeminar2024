# QEDSeminar2024

## Editoren

### Web Editors

Zum Bearbeiten/Auswerten einer einzelnen Datei ist oftmals der Web Editor ausreichend.  Es gibt zwei Server mit im wesentlichen Identischen Editoren:

- https://lean.math.hhu.de/
- https://live.lean-lang.org/

Kurze Dateien lassen sich einfach durch Kopieren und Versenden der URL teilen. Längere Dateien kann man herunterladen.

### Lokale Installation

Um an Projekten zu arbeiten, die aus mehreren Dateien bestehen, kommt man meist an einer lokalen Installation von Lean nicht herum.  Der Editor mit der besten Unterstützung für die Entwicklung in Lean ist VS Code.  Die Installation von Lean und VS Code wird in folgender Installationsanleitung beschrieben:

https://leanprover-community.github.io/get_started.html

Nach erfolgreicher Installation ist der nächste Schritt, ein Projekt zu initialisieren:

https://leanprover-community.github.io/install/project.html


## Hilfe

### Spickzettel für Taktiken

[Floris van Doorn's Cheat Sheet](https://github.com/fpvandoorn/LeanCourse23/blob/master/lean-tactics.pdf) 
[Martin Dvorak's Cheat Sheet](https://github.com/madvorak/lean4-tactics)

Die Varianten mit Fragezeichen (`simp?`, `exact?`, `apply?`, `rw?`) kamen im Spiel nicht vor, sind aber sehr nützlich – einfach mal ausprobieren!  Auch `aesop` kann Beweise abkürzen.


### mathlib-Bibliothek

Die offizielle Dokumentation von mathlib findet man unter  https://leanprover-community.github.io/mathlib4_docs/.  Es gibt dort auch eine rudimentäre Suchfunktion.  
Besser sucht man allerdings mit [Loogle](https://loogle.lean-lang.org/). Um zum Beispiel den Satz

    theorem imp_iff_not_or : A → B ↔ ¬A ∨ B

in `mathlib` zu finden, würde man `(_ → _ ) ↔ (¬ _ ∨ _)` Looglen.  (Das funktioniert auch.)
Loogle versteht `-> und `<->` anstelle von `→` und `↔`.  Um Suchanfragen mit anderen Unicode-Symbolen zu formulieren, muss man die Anfrage zunächst in einem externen Editor (oder dem Web Editor) formulieren und nach Loogle kopieren.

### Zulip

Es gibt eine sehr freundliche weltweite Lean/mathlib-Community, die rund um die Uhr Fragen beantwortet.  

https://leanprover.zulipchat.com/

Um Fragen zu stellen, muss man sich allerdings zunächst einen Account auf Zulip zulegen.  Die erste Anlaufstelle ist dann der `new members`-Kanal:

https://leanprover.zulipchat.com/#narrow/stream/113489-new-members

