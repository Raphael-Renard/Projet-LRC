
:- discontiguous concept/1.

% Vérification sémantique :                                                │
concept(C) :- cnamea(C). % concepts atomique
concept(CG) :- cnamena(CG). % non atomique
instance(I) :- iname(I). % identificateurs d instance
role(R) :- rname(R). % identificateurs de rôle.

% la grammaire de  ALC 
concept(not(C)) :- concept(C).
concept(and(C1, C2)) :- concept(C1), concept(C2).
concept(or(C1, C2)) :- concept(C1), concept(C2).
concept(some(R, C)) :- role(R), concept(C).
concept(all(R, C)) :- role(R), concept(C).

% Vérification syntaxique Tbox et Abox concept et role                                                
definition(CA, CG) :- cnamena(CA), concept(CG).
verify_tbox([]).
verify_tbox([(CA, CG) | Q]) :-  definition(CA, CG), verify_tbox(Q).

instanciationC(I, CG) :- instance(I), concept(CG).
instanciationR(I1, I2, R) :- instance(I1), instance(I2), role(R).
verify_aboxConcept([]).
verify_aboxConcept([(I, CG) | Q]) :- instanciationC(I, CG), verify_aboxConcept(Q).
verify_aboxRole([]).
verify_aboxRole([(I1, I2, R) | Q]) :- instanciationR(I1, I2, R), verify_aboxRole(Q).
verif_Abox(AboxC,AboxR) :- verify_aboxConcept(AboxC), verify_aboxRole(AboxR).

% Auto-référencement                       
non_circular([]).
non_circular([C|L]) :- equiv(C, Def_C), autoref(C, Def_C), non_circular(L).

autoref(_, Def) :- cnamea(Def).
autoref(C, Def) :- C \== Def, cnamena(Def), equiv(Def, Def_developpe), autoref(C, Def_developpe).
autoref(C, and(D1,D2)) :- autoref(C, D1), autoref(C, D2).
autoref(C, or(D1,D2)) :- autoref(C, D1), autoref(C, D2).
autoref(C, all(_,D)) :- autoref(C,D).
autoref(C, some(_,D)) :- autoref(C,D).
autoref(C, not(D)) :- autoref(C,D).
	
% Traitement des Boxs 
developpe(C, C) :- cnamea(C).
developpe(C, D) :- equiv(C, E), developpe(E, D).
developpe(not(C), not(D)) :- developpe(C, D).
developpe(or(C1,C2), or(D1,D2)) :-  developpe(C1, D1),  developpe(C2, D2).
developpe(and(C1,C2),and(D1,D2)) :-  developpe(C1,D1), developpe(C2,D2).
developpe(some(R,C), some(R,D)) :- developpe(C, D).
developpe(all(R,C), all(R,D)) :- developpe(C, D).

% traitement de Tbox et traitement de Abox
transforme([], []).
transforme([(X,C) | L], [(X,D) | M]) :-  developpe(C, E), nnf(E, D), transforme(L, M).

nnf(not(and(C1,C2)),or(NC1,NC2)) :- nnf(not(C1),NC1), nnf(not(C2),NC2),!.
nnf(not(or(C1,C2)),and(NC1,NC2)) :- nnf(not(C1),NC1),nnf(not(C2),NC2),!.
nnf(not(all(R,C)),some(R,NC)) :- nnf(not(C),NC),!.
nnf(not(some(R,C)),all(R,NC)) :- nnf(not(C),NC),!.
nnf(not(not(X)),X) :- !.
nnf(not(X),not(X)) :- !.
nnf(and(C1,C2),and(NC1,NC2)) :- nnf(C1,NC1),nnf(C2,NC2),!.
nnf(or(C1,C2),or(NC1,NC2)) :- nnf(C1,NC1), nnf(C2,NC2),!.
nnf(some(R,C),some(R,NC)) :-nnf(C,NC),!.
nnf(all(R,C),all(R,NC)) :-  nnf(C,NC),!.
nnf(X,X).