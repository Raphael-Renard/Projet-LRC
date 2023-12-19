premiere_etape(Tbox, Abi, Abr) :-
    setof((CA, CG), equiv(CA, CG), Tboxt),      
    setof((I1, I2), inst(I1, I2), Abit),        
    setof((I1, I2, R), instR(I1, I2, R), Abr), 
    (verif_Tbox(Tboxt) ->
        write('[LOG] Vérification de la TBox réussi'), nl;
        write('[ERREUR] Il y a erreur de syntaxe dans la TBox'), nl, halt),
    
    % Vérification de la Abox
    (verif_Abox(Abit,Abr) ->
        write('[LOG] Vérification de la ABox réussi'), nl;
        write('[ERREUR] Il y a erreur de syntaxe dans la ABox'), nl, halt),
    
    % Vérification des auto-référencements
    setof(X, cnamena(X), Lcc),    % Récupération de la liste des concepts non atomiques
    (verif_Autoref(Lcc) ->
        write('[LOG] Il n\'y a pas auto-référencement dans la TBox'), nl ;
        write('[ERREUR] Il y a auto-référencement dans la TBox'), nl, halt),

    transforme(Abit, Abi),
    %write('abi:'), write(Abi), nl,
    %write('abit:'), write(Abit),nl,
    transforme(Tboxt, Tbox),
    %write('Tbox:'), write(Tbox), nl,
    %write('Tboxt:'), write(Tboxt),nl,
    write('[LOG] Transformation finie'),nl.

deuxieme_etape(Abi,Abi1,Tbox) :-
    saisie_et_traitement_prop_a_demontrer(Abi,Abi1,Tbox).

saisie_et_traitement_prop_a_demontrer(Abi,Abi1,Tbox) :- nl,
    write('Entrez le numéro du type de proposition que vous voulez démontrer :'), nl,
    write('1 Une instance donnée appartient a un concept donné.'), nl,
    write('2 Deux concepts qui n\'ont pas d\'éléments en commun (ils ont une intersection vide).'), nl,
    read(R),
    suite(R,Abi,Abi1,Tbox).

suite(1,Abi,Abi1,Tbox) :- acquisition_prop_type1(Abi,Abi1,Tbox), !.
suite(2,Abi,Abi1,Tbox) :- acquisition_prop_type2(Abi,Abi1,Tbox), !.
suite(_,Abi,Abi1,Tbox) :- nl, 
    write('Cette réponse est incorrecte.'), nl,
    saisie_et_traitement_prop_a_demontrer(Abi,Abi1,Tbox).

troisieme_etape(Abi,Abr) :-
    tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls),
    write('====================='),nl,nl,
    resolution(Lie,Lpt,Li,Lu,Ls,Abr).

projet :-
    load_files('fonctionsAnnexe.pl'),
    load_files('partie1.pl'),
    load_files('partie2.pl'),
    load_files('partie3.pl'),
    load_files('T-abox_tbox.pl'),
    premiere_etape(Tbox, Abi, Abr),             % Call de la première partie
    deuxieme_etape(Abi,Abi1,Tbox),
    (troisieme_etape(Abi1,Abr)->
    	write('Il y a une feuille ouverte : on n\'a pas pu démontré la proposition');
    	write('Toutes les feuilles sont fermées : on a démontré la proposition')),nl.

projet.