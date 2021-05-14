/* ENT_roles
* Author: REMI DECOUTY, DAMIEN LU
* Creation date: 13/05/2021
*/
MACHINE
    ENT_roles
    
    
SEES
    ENT_data
    
    
SETS
    ROLES = {Enseignant, Responsable, Directeur, Etudiant, Membre_jury};
    
    /* consulter_note_promo : le directeur peut consulter les notes de tous les étudiants
    consulter_note_etu : un étudiant peut consulter les notes des UE auxquelles il est inscrit
    consulter_respo_ue : un responsable d'UE peut consulter les notes de tous les étudiants inscrits aux UEs dont-il est le responsable */
    
    PERMISSIONS = {consulter_note_promo, consulter_note_etu, consulter_note_respo_ue , saisir_resultat_semestre, saisir_note_ue, consulter_validation_promo, 
    consulter_validation_etu}       
    
    
VARIABLES
    roleOf,    
    currentUser,
    Session
    
    
INVARIANT
    roleOf : PERSONNES --> POW(ROLES) &
    currentUser : PERSONNES & 
    Session : PERSONNES <-> ROLES
    
    
INITIALISATION
    
    roleOf :=
    {
        (ENS_1|->{Enseignant}),(ENS_2|->{Enseignant}),(ENS_3|->{Enseignant}),(ENS_4|->{Enseignant}),(ENS_5|->{Enseignant}),
        (ENS_6|->{Enseignant}),(ENS_7|->{Enseignant}),(ENS_8|->{Enseignant}),(ENS_9|->{Enseignant}),
        
        (DIRECTEUR|->{Directeur}),
        
        (E1|->{Etudiant}),(E2|->{Etudiant}),(E3|->{Etudiant}),(E4|->{Etudiant}),(E5|->{Etudiant}),(E6|->{Etudiant}),(E7|->{Etudiant}),(E8|->{Etudiant}),(E9|->{Etudiant}),
        (E10|->{Etudiant}),(E11|->{Etudiant}),(E12|->{Etudiant}),(E13|->{Etudiant}),(E14|->{Etudiant}),(E15|->{Etudiant}),(E16|->{Etudiant}),(E17|->{Etudiant}),(E18|->{Etudiant}),            
        (E19|->{Etudiant}),(E20|->{Etudiant}),(none |-> {})
    } ||

    currentUser := none  || 
    
    Session:={}
    
    
OPERATIONS
    
    connect(user,roleSet) = 
    PRE
        user : PERSONNES & user /: dom(Session) & roleSet : POW1(ROLES) & roleSet <: roleOf(user)
    THEN
        Session := Session\/({user}*roleSet) ||
        currentUser := user
    END;
    
    
    disconnect(user) = 
    PRE
        user : PERSONNES & user:dom(Session) & user = currentUser
    THEN
        Session := {user}<<|Session ||
        currentUser := none
    END;
    
    
    changeRole (user, role) = 
    PRE
        user : PERSONNES  & role : ROLES
    THEN
        roleOf := roleOf <+ {user|->{role}}	
    END
    
END
