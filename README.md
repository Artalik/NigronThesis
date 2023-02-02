# NigronThesis
# Travaux de thèse

Ce dépot contient les différents travaux présentés dans le manuscrit.

## Installation

Les dépendances des travaux peuvent être installées ainsi avec opam sur la version 4.13.0 de OCaml :

`opam repo add coq-released https://coq.inria.fr/opam/released`

`opam install coq.8.15.2 coq-iris.4.0.0 coq-equations.1.3+8.15`

Le `Makefile` compile l'ensemble des travaux excepté l'expérimentation sur CompCert.

Pour compiler l'expérimentation sur CompCert, il faut également installer les dépendances de CompCert et suivre la démarche usuelle du compilateur (`./configure` puis `make`).

## Structure

`src/lib/SepLogic` contient la définition de la logique de séparation, l'instantiation à MoSel et diverses tactiques et lemmes.

`src/lib/FM` contient la définition de la monade libre

`src/fresh/relabels` contient l'expérimentation sur le ré-étiquetage d'arbre

`src/fresh/CompCert` contient la compilateur CompCert avec l'expérimentation sur le module SimplExpr

`src/fresh/CoqNom/examples` contient les exemples relatifs à l'analyse de données

`src/fresh/CoqNom/src/Formalisation` contient la formalisation de Nom

`src/fresh/CoqNom/src/Formalisation/ZeroCopy` contient la logique de programme

`src/fresh/CoqNom/src/Formalisation/Formats` contient les décodeurs des protocoles Radius, SSH et Ipsec.

`src/fresh/CoqNom/src/Raffinement` contient tout ce qu'il est relatif au raffinement

`src/fresh/CoqNom/src/Extraction` contient le code relatif à la compilation vers C.

## Exemples

Trois exemples de protocoles sont disponibles, les codes ont directement été adaptés de ceux de la bibliothèque rusticata :

`src/fresh/CoqNom/src/Formalisation/Formats` contient un dossier pour chaque format.

Les fichiers nommées `*_spec.v` contiennent les preuves relatives au zéro-copie.

Les fichiers nommées `*_rel.v` contiennent le raffinement des décodeurs.

Radius possède deux versions du raffinement, celle dans le dossier `src/fresh/CoqNom/src/Formalisation/Formats/Radius/versionUnknown` appelle directement des structures C pré-existantes.

SSH contient deux versions différentes : `parser.v` a été adapté depuis suricata alors `ssh.v` a été adapté de rusticata.

Ipsec n'a pas été raffiné, la version de rusticata se heurtent aux limitations décrites dans le manuscrit.

La version C de Radius (obtenu par extraction puis avec le compilateur) est disponible ici : `src/fresh/CoqNom/src/Extraction/C/RadiusC/parser_Radius.c`

La version C de SSH vient de `ssh.v` et est disponible ici : `src/fresh/CoqNom/src/Extraction/C/SSHC/parser_ssh.c`
