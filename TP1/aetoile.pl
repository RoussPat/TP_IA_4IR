%*******************************************************************************
%                                    AETOILE
%*******************************************************************************

/*
Rappels sur l'algorithme
 
- structures de donnees principales = 2 ensembles : P (etat pendants) et Q (etats clos)
- P est dedouble en 2 arbres binaires de recherche equilibres (AVL) : Pf et Pu
 
   Pf est l'ensemble des etats pendants (pending states), ordonnes selon
   f croissante (h croissante en cas d'egalite de f). Il permet de trouver
   rapidement le prochain etat a developper (celui qui a f(U) minimum).
   
   Pu est le meme ensemble mais ordonne lexicographiquement (selon la donnee de
   l'etat). Il permet de retrouver facilement n'importe quel etat pendant

   On gere les 2 ensembles de façon synchronisee : chaque fois qu'on modifie
   (ajout ou retrait d'un etat dans Pf) on fait la meme chose dans Pu.

   Q est l'ensemble des etats deja developpes. Comme Pu, il permet de retrouver
   facilement un etat par la donnee de sa situation.
   Q est modelise par un seul arbre binaire de recherche equilibre.

Predicat principal de l'algorithme :

   aetoile(Pf,Pu,Q)

   - reussit si Pf est vide ou bien contient un etat minimum terminal
   - sinon on prend un etat minimum U, on genere chaque successeur S et les valeurs g(S) et h(S)
	 et pour chacun
		si S appartient a Q, on l'oublie
		si S appartient a Pu (etat deja rencontre), on compare
			g(S)+h(S) avec la valeur deja calculee pour f(S)
			si g(S)+h(S) < f(S) on reclasse S dans Pf avec les nouvelles valeurs
				g et f 
			sinon on ne touche pas a Pf
		si S est entierement nouveau on l'insere dans Pf et dans Pu
	- appelle recursivement etoile avec les nouvelles valeurs NewPF, NewPu, NewQs

*/

%*******************************************************************************

:- ['avl.pl'].       % predicats pour gerer des arbres bin. de recherche   
:- ['taquin.pl'].    % predicats definissant le systeme a etudier
:- set_prolog_stack(global, limit(100 000 000 000)).
:- set_prolog_stack(trail,  limit(20 000 000 000)).
:- set_prolog_stack(local,  limit(2 000 000 000)).

%*******************************************************************************

%*************************************************
%	Affichage de la solution : affiche_solution
%*************************************************

% Cas trivial
affiche_solution(U,_Q) :-
    initial_state(U),
    !.

% Si l'etat a deja ete developpe
affiche_solution(U,Q) :-
    not(initial_state(U)),
    belongs([U,[_,_,_],Pere,A],Q),
    affiche_solution(Pere,Q),
    write(A),
    write(" -> ").


%************************************************************
%	Determination des successeurs d'une situation et de leur
%   évalution : expand 
%************************************************************
expand(U,S,[_Fu,_Hu,Gu],[Fs,Hs,Gs],A) :-
    rule(A,Cost,U,S),
    Gs is Gu+Cost,
    heuristique(S,Hs),
    Fs is Gs + Hs.

% Remarque : cette solution permet de trouver 1 successeur, il faut donc utiliser le prédicat findall/3 pour trouver tous les successeurs dans aetoile/3.
/*
 Une alternative serait pour utiliser expand/3 directement dans aetoile/3 :
	
expand(Ls, U, [_,_,G]):- 
	findall([S,[Fs,Hs,Gs],U,Act],
			(rule(A,Cost,U,S), heuristique(S,Hs), Gs is G+Cost, Fs is Gs+Hs),
		 	Ls).
*/


%*********************************************************
%	Traitement des noeuds successeurs : loop_successors
%*********************************************************

loop_successors([],Pui,Pfi,Puf,Pff,_Q) :-
    Puf = Pui,
    Pff = Pfi.

loop_successors([[S,[Fs,Hs,Gs],U,A]|Rest],Pui,Pfi,Puf,Pff,Q):-
    % Si S est dans Q (deja developpe), on oublie cet etat
    (belongs([S,_,_,_],Q)->
        Puaux = Pui,
        Pfaux = Pfi
    ;
		% Si S est dans Pu, on garde le terme associe a la meilleure evaluation (dans Pu et Pf)
        (suppress([S,[Fs1,Hs1,Gs1],_OldPere,_OldA],Pui,Put)->
            ([Fs,Hs,Gs] @< [Fs1,Hs1,Gs1] ->
                suppress([[Fs1,Hs1,Gs1],S],Pfi,Pft),
                insert([[Fs,Hs,Gs],S],Pft,Pfaux),
                insert([S,[Fs,Hs,Gs],U,A],Put,Puaux)   
            ; %else
            Puaux = Pui,
            Pfaux = Pfi
            )
        ; 
		% Sinon on cree un nouveau terme a inserer dans Pu (et Pf)
        insert([[Fs,Hs,Gs],S],Pfi,Pfaux),
        insert([S,[Fs,Hs,Gs],U,A],Pui,Puaux)
        )
    ),
    loop_successors(Rest,Puaux,Pfaux,Puf,Pff,Q).
    

%*******************************************************************************

%*******************
%	Algorithme A*
%*******************

% Cas trivial : Pf et Pu sont vides
aetoile(Pf,Pu,_) :-
    empty(Pf),
    empty(Pu),
    writeln("PAS DE SOLUTION: L'ETAT FINAL N'EST PAS ATTEIGNABLE !").

%Cas trivial : le noeud minimal de Pf correspond a la situation finale
aetoile(Pf,Pu,Q) :-
    suppress_min([[Ff,Hf,Gf],FS],Pf,_Pf1),
    suppress([FS,[Ff,Hf,Gf],Pere,Au],Pu,_Pu1),
    final_state(FS),
    insert([FS,[Ff,Hf,Gf],Pere,Au],Q,Q1), % insert dans Q pour que l'affichage soit plus simple
    affiche_solution(FS,Q1).    

% Cas general
aetoile(Pf,Pu,Q) :-
    suppress_min([[Fu,Hu,Gu],U],Pf,Pf1),
    suppress([U,[Fu,Hu,Gu],Pere,Au],Pu,Pu1),
    write("["), 
	write(Fu), 
	write(","), 
	write(Hu), 
	write(","), 
	write(Gu), 
	write("]"),    
    write_state(U),
    
    findall([S,[Fs,Hs,Gs],U,A_new],
			(expand(U,S,[_,_,Gu],[Fs,Hs,Gs],A_new)),
			LS),
    loop_successors(LS,Pu1,Pf1,Pu2,Pf2,Q),    
    insert([U,[Fu,Hu,Gu],Pere,Au],Q,Q1),
    aetoile(Pf2,Pu2,Q1).

%*******************************************************************************

%***********
%	Main
%***********

main :-
	% Situation initiale
    initial_state(IS),

	% Calcul de F0, H0, G0 pour cette situation
    heuristique(IS,H0),
    G0 is 0,
    F0 is H0 + G0,

	% Initialisations Pf, Pu et Q 
    Pf = nil,
    Pu =nil,
    Q = nil,

	% Insertion des noeuds dans Pf et Pu
    insert([[F0,H0,G0],IS],Pf,Pf1),
    insert([IS,[F0,H0,G0],nil,nil],Pu,Pu1),

	% Lancement de Aetoile
    aetoile(Pf1,Pu1,Q).
	
%*******************************************************************************

%*************************
%	Tests de performance
%*************************

performance(Runtime) :-
    statistics(runtime, [Start,_]),
    main,
    statistics(runtime, [Stop,_]),
    Runtime is Stop - Start. % resultat en ms


%**********************
%	Tests unitaires
%**********************
	
% Test expand/3 sur la situation initiale
test_expand(LS,Pu2,Pf2,Q) :-
    initial_state(IS),
    heuristique(IS,H0),
    G0 is 0,
    F0 is H0 + G0,
    Pf = nil,
    Pu =nil,
    Q = nil,
    insert([[F0,H0,G0],IS],Pf,Pf1),
    insert([IS,[F0,H0,G0],nil,nil],Pu,Pu1),

    findall([S,[Fs,Hs,Gs],IS,A],expand(IS,S,[F0,H0,G0],[Fs,Hs,Gs],A),LS),
    loop_successors(LS,Pu1,Pf1,Pu2,Pf2,Q).


% A COMPLETER


/* A VOIR SI ON GARDE (javais ca dans mon code)

%Test sur la situation finale
test_expand2(S_list) :-
	final_state(U),
	heuristique(U,H),
	G=0,
	F is G+H,
	findall([S, Val_new, U, A], (expand(U, S, [F,H,G], Val_new, A)), S_list).

%LOOP_SUCCESSORS

test_ls(S_list, Pu_new, Pf_new, Q) :-
	initial_state(U),
	heuristique(U,H),
	G=0,
	F is G+H,
	Pf = nil,
	Pu = nil,
	Q = nil,
	insert([[F,H,G], U], Pf, Pf_new),
	insert([U, [F,H,G], nil, nil], Pu, Pu_new),	
	%expand(S_list,U,[F,H,G]).
	findall([S, Val_new, U, A], (expand(U, S, [F,H,G], Val_new, A)), S_list),
	loop_successors(S_list, Pu, Pf, Q, Pu_new, Pf_new).


%AFFICHE_SOLUTION

test_affiche :- 
	G= nil,
	insert(1, G, G1),
	insert(3, G1, G2),
	insert(4, G2, G3),
	insert(8, G3, G4),
	insert(6, G4, G5),	
	insert(2, G5, G6),
	put_flat(G6).

*/
   
