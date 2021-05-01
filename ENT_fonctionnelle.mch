/* ENT_fonctionnelle
* Author: REMI DECOUTY, DAMIEN LU
* Creation date: 01/05/2021
*/

MACHINE
    ENT_fonctionnelle
    
CONSTANTS 
    liste_ue, etudiants, enseignants, directeur
    
    
PROPERTIES
    etudiants <: FIN(PERSONNES) & enseignants <: FIN(PERSONNES) & directeur : FIN(PERSONNES) & liste_ue <: FIN(UE)
    
    
SETS
    UE; PERSONNES; VALIDATION_UE = {ue_valide, ue_valide_compensation, ue_non_valide}; VALIDATION_SEMESTRE = {valide, non_valide}; 
    PHASES = {phase_designation_ue, 
        phase_1_enregistrement_enseignants, phase_2_enregistrement_enseignants, 
        phase_inscription_etudiants, phase_verification_etudiants, phase_saisie_notes, 
        phase_1_jury, phase_2_jury, phase_3_jury, phase_4_jury, 
        phase_consultation_resultat}
    
    
VARIABLES
    ue_ouvertes, inscriptions, etudiants_inscrits, // etudiants_inscrits représente la liste des étudiants dont l'inscription est validée (7 UE)
    note, enseignants_ue, responsables_ue, 
    validations_ue, validations_semestre, 
    jury, nb_enseignant_restant, nb_enseignant_ue_non_enseigne, nb_enseignant_ue_enseigne, nb_etudiant_restant,
    notes_etu, validation_semestre_etu,
    phase_actuelle
    
    
INVARIANT
    ue_ouvertes <: liste_ue & 
    ue_ouvertes : FIN(ue_ouvertes) &
    inscriptions: etudiants <-> ue_ouvertes  & 
    etudiants_inscrits <: dom(inscriptions) & 
    note: inscriptions +-> 0..20  & 
    enseignants_ue : enseignants <-> ue_ouvertes  & 
    responsables_ue <: enseignants_ue  & 
    validations_ue : note +-> VALIDATION_UE & 
    validations_semestre : etudiants_inscrits +-> VALIDATION_SEMESTRE &
    jury <: FIN(PERSONNES) & 
    jury : FIN(jury) & 
    nb_enseignant_restant : NATURAL & 
    nb_enseignant_ue_non_enseigne : NATURAL&
    nb_enseignant_ue_enseigne : NATURAL &
    nb_etudiant_restant : NATURAL &
    notes_etu <: validations_ue &
    validation_semestre_etu <: validations_semestre &
    phase_actuelle : FIN(PHASES) &

    (phase_actuelle = {phase_1_enregistrement_enseignants} => card(ue_ouvertes) > 0) &
    (phase_actuelle = {phase_2_enregistrement_enseignants} => !ue. (ue : ue_ouvertes => card(enseignants_ue~(ue)) > 0)) &
    (phase_actuelle = {phase_inscription_etudiants} => !(ue,etu). (ue : ue_ouvertes & etu : etudiants => card(responsables_ue~(ue)) = 1)) &
    (phase_actuelle = {phase_verification_etudiants} => !etu. (etu : etudiants & etu : dom(inscriptions) => card(inscriptions[{etu}]) <= 7)) & 
    (phase_actuelle = {phase_saisie_notes} => !etu. (etu : etudiants_inscrits => card(inscriptions[{etu}]) = 7)) &
    (phase_actuelle = {phase_1_jury} => card(jury) <= 8) &
    (phase_actuelle = {phase_2_jury} => card(jury) = 8) &
    (phase_actuelle = {phase_3_jury} => !(etu,ue). (etu : etudiants_inscrits & ue : inscriptions[{etu}] =>  note(etu,ue) : 0..20)) &
    (phase_actuelle = {phase_4_jury} => !(etu,ue). (etu : etudiants_inscrits & ue : inscriptions[{etu}] =>  validations_ue(etu,ue,note(etu,ue)) : VALIDATION_UE)) &
    (phase_actuelle = {phase_consultation_resultat} => !(etu). (etu : etudiants_inscrits =>  validations_semestre(etu) : VALIDATION_SEMESTRE)) 
    
    
INITIALISATION
    ue_ouvertes, inscriptions, etudiants_inscrits := {},{},{} ||
    note, enseignants_ue, responsables_ue := {},{},{} ||
    validations_ue, validations_semestre := {},{} ||
    jury, nb_enseignant_restant, nb_enseignant_ue_non_enseigne, nb_enseignant_ue_enseigne,  nb_etudiant_restant := {directeur}, 5,2,3,2 ||
    notes_etu, validation_semestre_etu := {}, {} ||
    phase_actuelle := {phase_designation_ue} 
    
    
OPERATIONS
        
    Ouvrir_UE (ue) =
    PRE 
        ue : liste_ue &  ue /: ue_ouvertes & phase_actuelle = {phase_designation_ue}
    THEN 
        ue_ouvertes := ue_ouvertes \/ {ue}
    END;
    
    
    Ajouter_enseignant_UE (enseignant, ue) =
    PRE 
        ue : ue_ouvertes & enseignant : enseignants & ((enseignant |-> ue) /: enseignants_ue) & phase_actuelle = {phase_1_enregistrement_enseignants}
    THEN 
        enseignants_ue := enseignants_ue \/ {(enseignant |-> ue)}
    END;
    
    
    Ajouter_responsable_UE (responsable, ue) =
    PRE 
        ue : ue_ouvertes & responsable : enseignants & (responsable |-> ue) : enseignants_ue & ue /: ran(responsables_ue) &
        phase_actuelle = {phase_2_enregistrement_enseignants}
    THEN 
        responsables_ue := responsables_ue \/ {responsable |-> ue}
    END;
    
    
    Ajouter_inscription (etu, ue) = 
    PRE 
        etu : etudiants & etu /: etudiants_inscrits & ue : ue_ouvertes & (etu |-> ue) /: inscriptions & card(inscriptions[{etu}]) < 7 & 
        phase_actuelle = {phase_inscription_etudiants}
    THEN 
        inscriptions := inscriptions  \/ {etu |-> ue}
    END;
    
    
    Verification_inscription (etu) =
    PRE
        etu : etudiants & etu /: etudiants_inscrits & etu : dom(inscriptions)  & etu /: dom(dom(note)) & phase_actuelle = {phase_verification_etudiants}
    THEN
        IF 
            (card(inscriptions[{etu}])) = 7 
        THEN
            etudiants_inscrits := etudiants_inscrits \/ {etu}
        ELSE
            inscriptions := {etu} <<| inscriptions
        END
    END;
    
    
    Ajouter_note (etu, ue, no) =
    PRE 
        etu : etudiants_inscrits & ue : ue_ouvertes & no : 0..20  & (etu |-> ue) : inscriptions & (etu |-> ue) /: dom(note) & phase_actuelle = {phase_saisie_notes}
    THEN 
        note := note \/ {(etu |-> ue) |-> no}
    END; 
    
    
    Ajout_membre_jury (membre) = 
    PRE 
        membre : FIN(PERSONNES) & membre /: jury & card(jury) < 8 & phase_actuelle = {phase_1_jury}
    THEN
        IF 
            (membre : etudiants_inscrits) & (nb_etudiant_restant > 0) 
        THEN
            jury := jury \/ {membre} ||
            nb_etudiant_restant := nb_etudiant_restant - 1
        ELSIF 
            (membre : enseignants) & (nb_enseignant_restant > 0) 
        THEN
            IF 
                (membre /: dom(enseignants_ue)) & (nb_enseignant_ue_non_enseigne > 0) 
            THEN
                jury := jury \/ {membre} ||
                nb_enseignant_restant := nb_enseignant_restant - 1 ||
                nb_enseignant_ue_non_enseigne := nb_enseignant_ue_non_enseigne - 1
            ELSIF 
                (membre : dom(enseignants_ue)) & (nb_enseignant_ue_enseigne > 0) 
            THEN
                jury := jury \/ {membre} ||
                nb_enseignant_restant := nb_enseignant_restant - 1 ||
                nb_enseignant_ue_enseigne := nb_enseignant_ue_enseigne - 1
            END
        END
    END;
    
    Completer_note (etu, ue) =        // si une UE n'a pas de note à l'issue de la phase de saisie des notes, alors le jury met 0 automatiquement à celle-ci
    PRE
        etu : etudiants_inscrits & ue : ue_ouvertes & (etu |-> ue) : dom (note) & note(etu,ue) /: 0..20 & phase_actuelle = {phase_2_jury}
    THEN
        note := note \/ {(etu |-> ue) |-> 0}
    END;
    
    
    Validation_ue (etu, ue) =
    PRE
        etu : etudiants_inscrits & ue : ue_ouvertes & (etu |-> ue) : dom (note) & (etu |-> ue |-> note(etu, ue)): dom(validations_ue) & 
        validations_ue(etu,ue,note(etu,ue)) /: VALIDATION_UE & phase_actuelle = {phase_3_jury}
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
        etu : etudiants_inscrits & etu /: dom(validations_semestre) & phase_actuelle = {phase_4_jury}
    THEN
        IF 
            (!xx.(xx : inscriptions[{etu}] => validations_ue(etu,xx,note(etu,xx)) : {ue_valide, ue_valide_compensation})) 
        THEN 
            IF 
                (!xx.(xx : inscriptions[{etu}] => validations_ue(etu,xx,note(etu,xx)) : {ue_valide}))
            THEN
                validations_semestre := validations_semestre \/ {etu |-> valide}
            ELSIF 
                (!(ue1,ue2,ue3,ue4,ue5,ue6,ue7).(
                        ue1 : inscriptions[{etu}] & 
                        ue2 : (inscriptions[{etu}] - {ue1}) & 
                        ue3 : (inscriptions[{etu}] - ({ue1} \/ {ue2})) & 
                        ue4 : (inscriptions[{etu}] - ({ue1} \/ {ue2} \/ {ue3})) & 
                        ue5 : (inscriptions[{etu}] - ({ue1} \/ {ue2} \/ {ue3} \/ {ue4})) & 
                        ue6 : (inscriptions[{etu}] - ({ue1} \/ {ue2} \/ {ue3} \/ {ue4} \/ {ue5})) & 
                        ue7 : (inscriptions[{etu}] - ({ue1} \/ {ue2} \/ {ue3} \/ {ue4} \/ {ue5} \/ {ue6}))
                        => (note(etu,ue1) + note(etu,ue2) + note(etu,ue3) + note(etu,ue4) + note(etu,ue5) + note(etu,ue6) + note(etu,ue7)) >= 70))  
            THEN
                validations_semestre := validations_semestre \/ {etu |-> valide}    
            END
        ELSE 
            IF
                (!(ue1,ue2,ue3,ue4,ue5,ue6,ue7).(
                        ue1 : inscriptions[{etu}] & 
                        ue2 : (inscriptions[{etu}] - {ue1}) & 
                        ue3 : (inscriptions[{etu}] - ({ue1} \/ {ue2})) & 
                        ue4 : (inscriptions[{etu}] - ({ue1} \/ {ue2} \/ {ue3})) & 
                        ue5 : (inscriptions[{etu}] - ({ue1} \/ {ue2} \/ {ue3} \/ {ue4})) & 
                        ue6 : (inscriptions[{etu}] - ({ue1} \/ {ue2} \/ {ue3} \/ {ue4} \/ {ue5})) & 
                        ue7 : (inscriptions[{etu}] - ({ue1} \/ {ue2} \/ {ue3} \/ {ue4} \/ {ue5} \/ {ue6}))        // 66 équivaut à environ 9.5 moyenne générale
                        => (note(etu,ue1) + note(etu,ue2) + note(etu,ue3) + note(etu,ue4) + note(etu,ue5) + note(etu,ue6) + note(etu,ue7)) >= 66))
            THEN
                validations_semestre := validations_semestre \/ {etu |-> valide}
            ELSE
                validations_semestre := validations_semestre \/ {etu |-> non_valide}
            END
        END
    END;
    
    
    Consulter_notes (etu) = 
    PRE
        etu : etudiants_inscrits & phase_actuelle = {phase_consultation_resultat}
    THEN
        notes_etu :=  (({etu} <| inscriptions) <| note) <| validations_ue
    END;
    
    
    Consulter_validation_semestre (etu) = 
    PRE
        etu : dom(validations_semestre) & phase_actuelle = {phase_consultation_resultat}
    THEN
        validation_semestre_etu :=  {etu} <| validations_semestre
    END
    
END