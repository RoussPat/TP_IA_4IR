%:- lib(listut).       % Placer cette directive en commentaire si vous utilisez Swi-Prolog 
   
                      % Sinon ne pas modifier si vous utilisez ECLiPSe Prolog :
                      % -> permet de disposer du predicat nth1(N, List, E)
                      % -> permet de disposer du predicat sumlist(List, S)
                      % (qui sont predefinis en Swi-Prolog)

                      
%***************************
%DESCRIPTION DU JEU DU TAKIN
%***************************

   %********************
   % ETAT INITIAL DU JEU
   %********************   
   % format :  initial_state(+State) ou State est une matrice (liste de listes)


initial_state1([ [a, b, c],       % C'EST L'EXEMPLE PRIS EN COURS
                [h, f, g],       % 
                [d,vide,e] ]).   % h1=4,   h2=5,   f*=5


% AUTRES EXEMPLES POUR LES TESTS DE  A*


initial_state2([ [ a, b, c],        
                [ g, h, d],
                [vide,f, e] ]). % h2=2, f*=2

initial_state3([ [b, c, d],
                [a,vide,g],
                [f, h, e]  ]). % h2=10 f*=10

initial_state4([ [f, g, a],
                [h,vide,b],
                [d, c, e]  ]). % h2=16, f*=20

initial_state5([ [e, f, g],
                [d,vide,h],
                [c, b, a]  ]). % h2=24, f*=30 

initial_state6([ [a, b, c],
                [g,vide,d],
                [h, f, e]]). % etat non connexe avec l'etat final (PAS DE SOLUTION)

initial_state7([[b, a, f, i],
				[k, h, c, m],
				[d, g, n,o],
				[e, l, j, vide]]).

initial_state8([[a, b, c, d],
				[e, f, g, h],
				[i, j, k, l],
				[m, n, vide, o]]).


   %******************
   % ETAT FINAL DU JEU
   %******************
   % format :  final_state(+State) ou State est une matrice (liste de listes)
   


final_state4x4([[a, b, c, d],
				[e, f, g, h],
				[i, j, k, l],
				[m, n, o, vide]]).


final_state3x3([[a, b,  c],
             [h,vide, d],
             [g, f,  e]]).

    
			 
   %********************
   % AFFICHAGE D'UN ETAT
   %********************
   % format :  write_state(?State) ou State est une liste de lignes a afficher

write_state([]):-
    write("\n").
write_state([Line|Rest]) :-
    write(Line),
    write_state(Rest).
   



%**********************************************
% REGLES DE DEPLACEMENT (up, down, left, right)             
%**********************************************
   % format :   rule(+Rule_Name, ?Rule_Cost, +Current_State, ?Next_State)
   
rule(up,   1, S1, S2) :-
   vertical_permutation(_X,vide,S1,S2).

rule(down, 1, S1, S2) :-
   vertical_permutation(vide,_X,S1,S2).

rule(left, 1, S1, S2) :-
   horizontal_permutation(_X,vide,S1,S2).

rule(right,1, S1, S2) :-
   horizontal_permutation(vide,_X,S1,S2).

   %***********************
   % Deplacement horizontal            
   %***********************
    % format :   horizontal_permutation(?Piece1,?Piece2,+Current_State, ?Next_State)
	
horizontal_permutation(X,Y,S1,S2) :-
   append(Above,[Line1|Rest], S1),
   exchange(X,Y,Line1,Line2),
   append(Above,[Line2|Rest], S2).

   %***********************************************
   % Echange de 2 objets consecutifs dans une liste             
   %***********************************************
   
exchange(X,Y,[X,Y|List], [Y,X|List]).
exchange(X,Y,[Z|List1],  [Z|List2] ):-
   exchange(X,Y,List1,List2).

   %*********************
   % Deplacement vertical            
   %*********************
   
vertical_permutation(X,Y,S1,S2) :-
   append(Above, [Line1,Line2|Below], S1), % decompose S1
   delete(N,X,Line1,Rest1),    % enleve X en position N a Line1,   donne Rest1
   delete(N,Y,Line2,Rest2),    % enleve Y en position N a Line2,   donne Rest2
   delete(N,Y,Line3,Rest1),    % insere Y en position N dans Rest1 donne Line3
   delete(N,X,Line4,Rest2),    % insere X en position N dans Rest2 donne Line4
   append(Above, [Line3,Line4|Below], S2). % recompose S2 

   %***********************************************************************
   % Retrait d'une occurrence X en position N dans une liste L (resultat R) 
   %***********************************************************************
   % use case 1 :   delete(?N,?X,+L,?R)
   % use case 2 :   delete(?N,?X,?L,+R)   
   
delete(1,X,[X|L], L).
delete(N,X,[Y|L], [Y|R]) :-
   delete(N1,X,L,R),
   N is N1 + 1.


   
   
   %*******************************************************************
   % Coordonnees X(colonne),Y(Ligne) d'une piece P dans une situation U
   %*******************************************************************
	% format : coordonnees(?Coord, +Matrice, ?Element)
	% Définit la relation entre des coordonnees [Ligne, Colonne] et un element de la matrice
	/*
	Exemples
	
	?- coordonnees(Coord, [[a,b,c],[d,e,f]],  e).        % quelles sont les coordonnees de e ?
	Coord = [2,2]
	yes
	
	?- coordonnees([2,3], [[a,b,c],[d,e,f]],  P).        % qui a les coordonnees [2,3] ?
	P=f
	yes
	*/

	
coordonnees([L,C], Mat, Elt) :-    
    nth1(L,Mat,Ligne), 
    nth1(C,Ligne, Elt).										

											 
   %*************
   % HEURISTIQUES
   %*************
   
heuristique(U,H, Fin) :-
%   heuristique1(U, H, Fin).  % au debut on utilise l'heuristique 1 
   heuristique2(U, H, Fin).  % ensuite utilisez plutot l'heuristique 2  
   
   
   %****************
   %HEURISTIQUE no 1
   %****************
   
   % Nombre de pieces mal placees dans l'etat courant U
   % par rapport a l'etat final F
    heuristique1(U, H, Fin) :-
        findall(P, (nth1(L,U,L1), nth1(C,L1, P), nth1(L,Fin,L2), nth1(C,L2,P), P\=vide) ,T),
        findall(Q,(nth1(L,U,L1), nth1(C,L1, Q), Q\=vide),R),
        length(T,Tl),
        length(R,Rl),
        H is Rl-Tl.

/*	 Alternative : évaluation récursive du nombre de différences entre deux matrices 

heuristique1(U, H) :-
    final_state(Fin),
    diff_matrice(U,Fin,H).

diff_matrice([],[],0).
diff_matrice([L1|R1],[L2|R2], H) :-
    diff_ligne(L1, L2, D),
    diff_matrice(R1, R2, H1),
    H is D+H1.

diff_ligne([],[],0).
diff_ligne([X1|Y1], [X2|Y2], H) :-
    diff_el(X1,X2,D),
    diff_ligne(Y1,Y2,H1),
    H is D+H1.


diff_el(vide,_,0).
diff_el(X,X,0):- 
    X\=vide.
diff_el(X,Y,1) :-
    X\=Y,
    X\=vide.

	*/

   
   
   %****************
   %HEURISTIQUE no 2
   %****************
   
   % Somme des distances de Manhattan à parcourir par chaque piece
   % entre sa position courante et sa positon dans l'etat final

   
    heuristique2(U, H, Fin) :-
        findall(D,(coordonnees([Li,Ci],U,P),
				   P\=vide, 
				   coordonnees([Lf,Cf],Fin,P),
				   D is abs(Li-Lf) + abs(Ci-Cf)),ListD),
        sumlist(ListD,H).   
        


