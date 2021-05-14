/* ENT_fonctionnelle
* Author: REMI DECOUTY, DAMIEN LU
* Creation date: 01/05/2021
*/

MACHINE
    ENT_fonctionnelle
    

SEES 
    ENT_data
 
    
PROPERTIES
    etudiants = {E1,E2,E3,E4,E5,E6,E7,E8,E9,E10,E11,E12,E13,E14,E15,E16,E17,E18,E19,E20} & 
    enseignants = {ENS_1,ENS_2,ENS_3,ENS_4,ENS_5,ENS_6,ENS_7,ENS_8,ENS_9} & 
    directeur = {DIRECTEUR} & 
    liste_ue = UE
    
    
VARIABLES
    ue_ouvertes, inscriptions,
    note, enseignants_ue, responsables_ue, 
    validations_ue, validations_semestre, 
    jury, nb_enseignant_restant, nb_enseignant_ue_non_enseigne, nb_enseignant_ue_enseigne, nb_etudiant_restant
    
    
INVARIANT
    ue_ouvertes <: liste_ue & 
    ue_ouvertes : FIN(ue_ouvertes) &
    inscriptions: etudiants <-> ue_ouvertes  & 
    note: inscriptions +-> 0..20  & 
    enseignants_ue : enseignants <-> ue_ouvertes  &
    responsables_ue <: enseignants_ue  &
    validations_ue : note +-> VALIDATION_UE & 
    validations_semestre : etudiants +-> VALIDATION_SEMESTRE &
    jury <: PERSONNES & 
    jury : FIN(jury) & 
    nb_enseignant_restant : NATURAL & 
    nb_enseignant_ue_non_enseigne : NATURAL &
    nb_enseignant_ue_enseigne : NATURAL &
    nb_etudiant_restant : NATURAL
    
    
INITIALISATION
    ue_ouvertes, inscriptions := {},{} ||
    note, enseignants_ue, responsables_ue := {},{},{} ||
    validations_ue, validations_semestre := {}, {} ||
    jury, nb_enseignant_restant, nb_enseignant_ue_non_enseigne, nb_enseignant_ue_enseigne,  nb_etudiant_restant := {DIRECTEUR} ,5,2,3,2
    
    
OPERATIONS
    
    Ouvrir_UE (ue) =
    PRE 
        ue : liste_ue &  ue /: ue_ouvertes
    THEN 
        ue_ouvertes := ue_ouvertes \/ {ue} 	
    END;
    
    
    Ajouter_enseignant_UE (enseignant, ue) =
    PRE 
        ue : ue_ouvertes & enseignant : enseignants & ((enseignant |-> ue) /: enseignants_ue) & card(ue_ouvertes) >= 7 & enseignant /: {ENS_8, ENS_9}
    THEN 
        enseignants_ue := enseignants_ue \/ {(enseignant |-> ue)}      // ENS_8 et ENS_9 ne doivent pas enseignés l'une des UE ouvertes, afin d'être dans le jury
    END;
    
    
    Ajouter_responsable_UE (responsable, ue) =
    PRE 
        ue : ue_ouvertes & responsable : enseignants & (responsable |-> ue) : enseignants_ue & 
        ue /: ran(responsables_ue) & !ue. (ue : ue_ouvertes => card(enseignants_ue~[{ue}]) > 0)
    THEN 
        responsables_ue := responsables_ue \/ {responsable |-> ue}
    END;
    
    
    Ajouter_inscription (etu, ue) = 
    PRE 
        etu : etudiants & ue : ue_ouvertes & (etu |-> ue) /: inscriptions & card(inscriptions[{etu}]) < 7 &  !ue. (ue : ue_ouvertes => card(responsables_ue~[{ue}]) = 1)
    THEN 
        inscriptions := inscriptions  \/ {etu |-> ue}
    END;
    
    
    Ajouter_note (etu, ue, no) =
    PRE 
        !etu. (etu : dom(inscriptions) => card(inscriptions[{etu}]) = 7) &
        etu : etudiants & ue : ue_ouvertes &  (etu |-> ue) : inscriptions & (etu |-> ue) /: dom(note)  & no : 0..20
    THEN 
        note := note \/ {(etu |-> ue) |-> no}
    END;
    
    
    Ajout_membre_jury (membre) = 
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
        IF
            membre : etudiants & nb_etudiant_restant > 0
        THEN
            jury := jury \/ {membre} ||
            nb_etudiant_restant := nb_etudiant_restant - 1
        ELSIF 
            membre : enseignants & nb_enseignant_restant > 0 
        THEN
            IF 
                membre /: dom(enseignants_ue) & nb_enseignant_ue_non_enseigne > 0
            THEN
                jury := jury \/ {membre} ||
                nb_enseignant_restant := nb_enseignant_restant - 1 ||
                nb_enseignant_ue_non_enseigne := nb_enseignant_ue_non_enseigne - 1
            ELSIF 
                membre : dom(enseignants_ue) & nb_enseignant_ue_enseigne > 0
            THEN
                jury := jury \/ {membre} ||
                nb_enseignant_restant := nb_enseignant_restant - 1 ||
                nb_enseignant_ue_enseigne := nb_enseignant_ue_enseigne - 1
            END
        END
    END;
    
        
    
    Validation_ue (etu, ue) =
    PRE
        etu : etudiants & ue : ue_ouvertes & (etu |-> ue) : dom (note)  & 
        !(etu,ue). (etu : etudiants & ue : ue_ouvertes & (etu |-> ue) : dom (note)  => note(etu,ue) : ran(note)) & 
        (etu |-> ue |-> note(etu, ue)) /: dom(validations_ue) & card(jury) = 8
    THEN
        IF 
            note(etu, ue) >= 10 
        THEN 
            validations_ue := validations_ue \/ {(etu |-> ue |-> note(etu, ue)) |-> ue_valide}
        ELSIF 
            note(etu, ue) >= 8 & note(etu, ue) < 10 
        THEN
            validations_ue := validations_ue \/ {(etu |-> ue |-> note(etu, ue)) |-> ue_valide_compensation} 
        ELSE 
            validations_ue := validations_ue \/ {(etu |-> ue |-> note(etu, ue)) |-> ue_non_valide} 
        END 
    END;
    
    
    Validation_semestre_etudiant (etu) =
    PRE
        etu : etudiants & etu /: dom(validations_semestre) & !(ue).(ue:inscriptions[{etu}] => (etu |-> ue) : dom (note)) &
        !(etu,ue). (etu : etudiants & ue : inscriptions[{etu}] & (etu |-> ue) : dom (note) => (etu |-> ue |-> note(etu, ue)) :  dom (validations_ue)) & card(jury) = 8
    THEN
        IF 
            (!ue.(ue : inscriptions[{etu}] => validations_ue(etu,ue,note(etu,ue)) : {ue_valide,ue_valide_compensation}))
        THEN
            IF
                SIGMA (ue).(ue:inscriptions[{etu}] | note(etu,ue)) >= 66                                /* l'étudiant à plus de 9.5 de moyenne générale  
                                                                                                           et toutes ses UE sont validées ou compensées */
            THEN
                validations_semestre := validations_semestre \/ {etu |-> valide}
            ELSE
                validations_semestre := validations_semestre \/ {etu |-> non_valide}
            END
        ELSE                                                                               // si l'étudiant à au moins une UE non_valide alors le semestre n'est pas validé
             validations_semestre := validations_semestre \/ {etu |-> non_valide}  
        END
        
    END;
    
    
    notes_etu <-- Consulter_notes (etu) = 
    PRE
        etu : dom(validations_semestre) & !etu. (etu : etudiants =>  etu : dom(validations_semestre))
    THEN
        notes_etu :=  (({etu} <| inscriptions) <| note) <| validations_ue
    END;
    
    
    validation_semestre_etu <-- Consulter_validation_semestre (etu) = 
    PRE
        etu : dom(validations_semestre) & !etu. (etu : etudiants =>  etu : dom(validations_semestre))
    THEN
        validation_semestre_etu :=  {etu} <| validations_semestre
    END
       
END
