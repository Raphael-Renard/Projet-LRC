# Démonstrateur ALC en Prolog

## Description

Ce projet implémente un démonstrateur en Prolog basé sur l'algorithme des tableaux pour la logique de description ALC. L'algorithme construit un arbre de démonstration en appliquant récursivement des règles, permettant ainsi de vérifier la satisfaisabilité d'un ensemble de formules.

## Algorithme

L'algorithme repose sur les principes suivants :

- **Branches** : 
  - Une branche est fermée si elle contient deux assertions contradictoires (a : A et a : ¬A).
  - Une branche est complète si aucune règle ne peut s'appliquer.
- **Arrêt de l'algorithme** : 
  - L'algorithme se termine si toutes les branches sont fermées ou si une branche est complète.
- **Insatisfaisabilité** : 
  - Un ensemble de formules F est insatisfaisable si toutes les branches de l'arbre sont fermées.

## Structure du Programme

### Partie 1 : Vérification et mise en forme

Cette partie s'occupe de la vérification syntaxique et sémantique de la Tbox (terminologie) et de la Abox (assertions), en utilisant des prédicats Prolog tels que :
- `equiv(ConceptNonAtom, ConceptGen)`
- `inst(Instance, ConceptGen)`
- `instR(Instance1, Instance2, role)`

### Partie 2 : Saisie de la proposition à démontrer

Deux types de propositions peuvent être prouvées :
1. **Appartenance d'une instance à un concept** : I : C.
2. **Intersection vide de deux concepts** : C1 ⊓ C2 ⊑ ⊥.

### Partie 3 : Démonstration de la proposition

Cette partie constitue le cœur du démonstrateur, mettant en œuvre l'algorithme de résolution basé sur la méthode des tableaux. L'arbre de résolution est construit à partir des assertions de la Abox étendue, et les règles de développement sont appliquées pour prouver la proposition initiale.
