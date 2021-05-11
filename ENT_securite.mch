/* ENT_securite
 * Author: REMI DECOUTY, DAMIEN LU
 * Creation date: 04/05/2021
 */

MACHINE
    ENT_securite
    
    
INCLUDES
    ENT_fonctionnelle
    
    
SETS
    ROLES = {Enseignant, Responsable, Directeur, Etudiant, Externe};
    
    /* 
    consulter_note_promo : le directeur peut consulter les notes de tous les étudiants
    consulter_note_etu : un étudiant peut consulter les notes des UE auxquelles il est inscrit
    consulter_respo_ue : un responsable d'UE peut consulter les notes de tous les étudiants inscrits à cette UE
    */
    PERMISSIONS = {consulter_note_promo, consulter_note_etu, consulter_note_respo_ue , saisir_note_ue, consulter_validation_promo, consulter_validation_etu}   
    


VARIABLES
    roleOf,    
    currentUser,
     Session,
     PermissionAssignement
     
INVARIANT
        roleOf : PERSONNES --> POW(ROLES) &
        currentUser : PERSONNES 
	& Session : PERSONNES<-> ROLES
	& !(uu).(uu:PERSONNES & uu:dom(Session)=> Session[{uu}]<:roleOf(uu))
	& PermissionAssignement : ROLES <-> PERMISSIONS


DEFINITIONS
    
    currentRole == (Session[{currentUser}])
        
        
INITIALISATION    
    roleOf := 
        {(ENS_1|->{Enseignant}),(ENS_2|->{Enseignant}),(ENS_3|->{Enseignant}),(ENS_3|->{Enseignant}),(ENS_4|->{Enseignant}),(ENS_5|->{Enseignant}),
        (ENS_6|->{Enseignant}),(ENS_7|->{Enseignant}),(ENS_8|->{Enseignant}),(ENS_9|->{Enseignant}),
        
        (DIRECTEUR|->{Directeur}),
        
        (E1|->{Etudiant}),(E2|->{Etudiant}),(E3|->{Etudiant}),(E4|->{Etudiant}),(E5|->{Etudiant}),(E6|->{Etudiant}),(E7|->{Etudiant}),(E8|->{Etudiant}),(E9|->{Etudiant}),
        (E10|->{Etudiant}),(E11|->{Etudiant}),(E12|->{Etudiant}),(E13|->{Etudiant}),(E14|->{Etudiant}),(E15|->{Etudiant}),(E16|->{Etudiant}),(E17|->{Etudiant}),(E18|->{Etudiant}),            
        (E19|->{Etudiant}),(E20|->{Etudiant}),(none |-> {})} ||
    
    currentUser := none  || 
    
    Session:={} ||
    
    PermissionAssignement := 
    {(Directeur |-> consulter_note_promo),(Directeur |-> consulter_validation_promo),
        
    (Enseignant |-> consulter_validation_promo),
    
    (Responsable |-> consulter_note_respo_ue),
    (Responsable |-> saisir_note_ue),
    
    (Etudiant |-> consulter_note_etu),
    (Etudiant |-> consulter_validation_etu)}

    
OPERATIONS   
    
    Ouvrir_UE_secure (ue) =
    PRE 
        ue : liste_ue &  ue /: ue_ouvertes
    THEN 
        Ouvrir_UE(ue)	
    END;
    
    
    Ajouter_enseignant_UE_secure (enseignant, ue) =
    PRE 
        ue : ue_ouvertes & enseignant : enseignants & ((enseignant |-> ue) /: enseignants_ue) & card(ue_ouvertes) >= 7 & enseignant /: {ENS_8, ENS_9}
    THEN 
        Ajouter_enseignant_UE(enseignant, ue)
    END;
    
    
    Ajouter_responsable_UE_secure (responsable, ue) =
    PRE 
        ue : ue_ouvertes & responsable : enseignants & (responsable |-> ue) : enseignants_ue & ue /: ran(responsables_ue) & 
        !ue. (ue : ue_ouvertes => card(enseignants_ue~[{ue}]) > 0)
    THEN 
        Ajouter_responsable_UE (responsable, ue) 
    END;
    
    
    Ajouter_inscription_secure (etu, ue) = 
    PRE 
        etu : etudiants & ue : ue_ouvertes & (etu |-> ue) /: inscriptions & card(inscriptions[{etu}]) < 7 &  !ue. (ue : ue_ouvertes => card(responsables_ue~[{ue}]) = 1)
    THEN 
         Ajouter_inscription (etu, ue)
    END;
    
    
    Ajouter_note_secure (etu, ue, no) =
    PRE 
        etu : etudiants & ue : ue_ouvertes & no : 0..20  & (etu |-> ue) : inscriptions &  (etu |-> ue)  /: dom(note) & 
        !etu. (etu : dom(inscriptions) => card(inscriptions[{etu}]) = 7)
    THEN 
        Ajouter_note (etu, ue, no)
    END;
    
    // TODO : ajouter les 3 enseignants des UE les plus suivies
    Ajout_membre_jury_secure (membre) = 
    PRE 
        membre : PERSONNES & 
        membre /: jury & 
        card(jury) < 8 &
        (card(jury) >= 2  => !(etu,ue). (etu : dom(inscriptions) & ue : inscriptions[{etu}] => (etu |-> ue: dom(note)))) &
        (membre : enseignants => nb_etudiant_restant = 0) &
        (membre : etudiants => membre : dom(inscriptions) & 
            card(inscriptions[{membre}]) = 7)
    THEN
       Ajout_membre_jury (membre)
    END;
    
    
    // TODO : une partie de la précondition fait planter ProB
    Validation_ue_secure (etu, ue) =
    PRE
        etu : etudiants & ue : ue_ouvertes & (etu |-> ue) : dom (note)  & (etu |-> ue) /: dom(dom(validations_ue)) & card(jury) = 8
        // & (etu |-> ue |-> note(etu, ue)): dom(validations_ue) & validations_ue(etu,ue,note(etu,ue)) /: VALIDATION_UE &
    THEN
	Validation_ue (etu, ue)
    END;
    
    
    // TODO  : intégrer la somme des moyennes
    Validation_semestre_etudiant_secure (etu) =
    PRE
        etu : dom(inscriptions) & etu /: dom(validations_semestre) & !(etu,ue). (etu : dom(inscriptions) & ue : inscriptions[{etu}] => (etu |-> ue: dom(dom(validations_ue))))
    THEN
	Validation_semestre_etudiant (etu)
    END;
    





    connect(user,roleSet) = 
    PRE
        user : PERSONNES & user/:dom(Session) 
		& roleSet:POW1(ROLES) & roleSet<:roleOf(user)  & card(dom(Session)) = 0 & user : etudiants
    THEN
        Session := Session\/({user}*roleSet) ||
        currentUser := user
    END;
    
    
    disconnect(user) = 
    PRE
        user : PERSONNES & user:dom(Session)  
    THEN
        Session := {user}<<|Session ||
       currentUser := none
    END;
    
    
    /* notes_etu <-- Consulter_notes_secure (etu) = 
    PRE
        etu : dom(validations_semestre) & !etu. (etu : etudiants =>  etu : dom(validations_semestre))
    THEN
        notes_etu :=  (({etu} <| inscriptions) <| note) <| validations_ue
    END; */
    
    
    validation_semestre_etu <-- Consulter_validation_semestre_secure (etu) = 
    PRE
        etu : dom(validations_semestre) & !etu. (etu : etudiants =>  etu : dom(validations_semestre))& currentUser = etu
    THEN 		
            validation_semestre_etu :=  {etu} <| validations_semestre
    END

    
END
