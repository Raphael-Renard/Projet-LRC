
:- discontiguous concept/1.

/* 
  Vérification sémantique :                                                
 */
concept(C) :- cnamea(C). %  concepts atomiques
concept(CG) :- cnamena(CG). %  concepts non atomiques
instance(I) :- iname(I). % identificateurs d instance
role(R) :- rname(R). % identificateurs de rôle.

% Grammaire de ALC
concept(not(C)) :- concept(C).
concept(and(C1, C2)) :- concept(C1), concept(C2).
concept(or(C1, C2)) :- concept(C1), concept(C2).
concept(some(R, C)) :- role(R), concept(C).
concept(all(R, C)) :- role(R), concept(C).

/* 
 Vérification de non-circularité dans la Tbox :                           
 */
non_circular([]).
non_circular([(Concept, Definition)|Rest]) :-
    not(member(Concept, Definition)),
    non_circular(Rest).

/* 
  Fonctions de vérification pour Tbox et Abox :                            
 */

verify_tbox([]).
verify_tbox([(Instance, Concept)|Rest]) :- instance(Instance), concept(Concept), verify_tbox(Rest), non_circular(Tbox).

verify_abox([]).
verify_abox([(Instance, Concept)|Rest]) :- instance(Instance), concept(Concept), verify_abox(Rest).

