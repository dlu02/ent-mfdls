/* ENT_securite
* Author: REMI DECOUTY, DAMIEN LU
* Creation date: 04/05/2021
*/

MACHINE
    ENT_securite

SEES 
    ENT_data
    
INCLUDES
    ENT_fonctionnelle, ENT_roles
    
    
PROMOTES 
    Ouvrir_UE, Ajouter_enseignant_UE, Ajouter_inscription, Validation_ue
    
    
VARIABLES
    PermissionAssignement
    
    
INVARIANT
    PermissionAssignement : ROLES <-> PERMISSIONS
    
    
DEFINITIONS
    
    currentRole == (Session[{currentUser}])
    
    
INITIALISATION    
    
    PermissionAssignement := 
    {
        (Directeur |-> saisir_resultat_semestre),
        (Directeur |-> consulter_note_promo),
        (Directeur |-> consulter_validation_promo),

        (Enseignant |-> consulter_validation_promo),
        
        (Responsable |-> saisir_note_ue),
        (Responsable |-> consulter_note_respo_ue),
        (Responsable |-> consulter_validation_promo),
        
        (Etudiant |-> consulter_note_etu),
        (Etudiant |-> consulter_validation_etu),
        
        (Membre_jury |-> consulter_note_promo)
    }
    
    
OPERATIONS   
    
    connectUser(user,roleSet) = 
    PRE
        user : PERSONNES & user /: dom(Session) 
        & roleSet:POW1(ROLES) & roleSet<:roleOf(user) & card(dom(Session)) = 0        
    THEN
        connect(user,roleSet)
    END;
    
    
    disconnectUser(user) = 
    PRE
        user : PERSONNES & user:dom(Session) & user = currentUser
    THEN
        disconnect(user)
    END;
    
    
    Ajouter_responsable_UE_secure (responsable, ue) =
    PRE 
        ue : ue_ouvertes & responsable : enseignants & (responsable |-> ue) : enseignants_ue & ue /: ran(responsables_ue) & 
        !ue. (ue : ue_ouvertes => card(enseignants_ue~[{ue}]) > 0)
    THEN 
        Ajouter_responsable_UE (responsable, ue) ||
        changeRole(responsable, Responsable)	
    END;
    
    
    Ajouter_note_secure (etu, ue, no) =
    PRE 
        etu : etudiants & ue : ue_ouvertes &  no : 0..20 & (etu |-> ue) : inscriptions & (etu |-> ue) /: dom(note) &
        !etu. (etu : dom(inscriptions) => card(inscriptions[{etu}]) = 7) &
        saisir_note_ue : PermissionAssignement[Session[{currentUser}]] &
        (currentUser |-> ue) : responsables_ue
    THEN
        Ajouter_note(etu, ue, no)
    END;
 
 
    Ajout_membre_jury_secure (membre) = 
    PRE 
        membre : PERSONNES & 
        membre /: jury & 
        card(jury) < 8 &
        (card(jury) >= 2  => !(etu,ue). (etu : dom(inscriptions) & ue : inscriptions[{etu}] => (etu |-> ue: dom(note)))) &
        (membre : enseignants => nb_etudiant_restant = 0) &
        (membre : etudiants => membre : dom(inscriptions) & 
            card(inscriptions[{membre}]) = 7) &
            membre /= none
    THEN
        Ajout_membre_jury (membre)
    END;
    
    
    Ajout_role_jury (membre) = 
    PRE 
        membre : (jury - {DIRECTEUR}) & (membre |-> {Membre_jury}) /: roleOf 
    THEN
        changeRole(membre, Membre_jury)
         
    END;
     
     
    Validation_semestre_etudiant_secure (etu) =
    PRE
        etu : etudiants & etu /: dom(validations_semestre) & !(ue).(ue:inscriptions[{etu}] => (etu |-> ue) : dom (note)) &
        !(etu,ue). (etu : etudiants & ue : inscriptions[{etu}] & 
        (etu |-> ue) : dom (note) => (etu |-> ue |-> note(etu, ue)) :  dom (validations_ue)) & card(jury) = 8 &
        saisir_resultat_semestre : PermissionAssignement[Session[{currentUser}]]
    THEN
        Validation_semestre_etudiant(etu)
    END;
    
    
    notes_etu <-- Consulter_notes_secure = 
    PRE
        !etu. (etu : etudiants =>  etu : dom(validations_semestre)) & currentUser /= none & card(dom(Session)) = 1 &
        (consulter_note_etu : PermissionAssignement[Session[{currentUser}]] or
        consulter_note_promo : PermissionAssignement[Session[{currentUser}]] or
        consulter_note_respo_ue : PermissionAssignement[Session[{currentUser}]])
    THEN
        IF consulter_note_etu : PermissionAssignement[Session[{currentUser}]]
        THEN
            notes_etu :=  (({currentUser} <| inscriptions) <| note) <| validations_ue
            
        ELSIF consulter_note_promo : PermissionAssignement[Session[{currentUser}]]
        THEN
            notes_etu := note <| validations_ue
            
        ELSIF consulter_note_respo_ue : PermissionAssignement[Session[{currentUser}]]
        THEN
            notes_etu :=  ((inscriptions |> responsables_ue[{currentUser}]) <| note) <| validations_ue
            
        END
        
    END;
    
    
    validation_semestre_etu <-- Consulter_validation_semestre_secure  = 
    PRE
        !etu. (etu : etudiants =>  etu : dom(validations_semestre)) & currentUser /= none & card(dom(Session)) = 1 &
        (consulter_validation_etu : PermissionAssignement[Session[{currentUser}]] or
        consulter_validation_promo : PermissionAssignement[Session[{currentUser}]])
    THEN 
        IF consulter_validation_etu : PermissionAssignement[Session[{currentUser}]]
        THEN
            validation_semestre_etu :=  {currentUser} <| validations_semestre
            
        ELSIF consulter_validation_promo : PermissionAssignement[Session[{currentUser}]]
        THEN
            validation_semestre_etu :=  validations_semestre
        END     
    END    
    
END
