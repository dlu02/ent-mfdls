/* ENT_data
* Author: REMI DECOUTY, DAMIEN LU
 * Creation date: 13/05/2021
 */
MACHINE
    ENT_data

CONSTANTS 
    liste_ue, etudiants, enseignants, directeur
    
SETS
    UE = {UE1,UE2,UE3,UE4,UE5,UE6,UE7,UE8,UE9,UE10};
    PERSONNES = {DIRECTEUR, ENS_1,ENS_2,ENS_3,ENS_4,ENS_5,ENS_6,ENS_7,ENS_8,ENS_9, E1,E2,E3,E4,E5,E6,E7,E8,E9,E10,E11,E12,E13,E14,E15,E16,E17,E18,E19,E20, none} ; 
    VALIDATION_UE = {ue_valide, ue_valide_compensation, ue_non_valide}; VALIDATION_SEMESTRE = {valide, non_valide};
    
    PHASES = {phase_designation_ue, 
    phase_1_enregistrement_enseignants, phase_2_enregistrement_enseignants, 
    phase_inscription_etudiants, phase_verification_etudiants, phase_saisie_notes, 
    phase_1_jury, phase_2_jury, phase_3_jury, 
    phase_consultation_resultat}

PROPERTIES
    etudiants = {E1,E2,E3,E4,E5,E6,E7,E8,E9,E10,E11,E12,E13,E14,E15,E16,E17,E18,E19,E20} & 
    enseignants = {ENS_1,ENS_2,ENS_3,ENS_4,ENS_5,ENS_6,ENS_7,ENS_8,ENS_9} & 
    directeur = {DIRECTEUR} & 
    liste_ue = UE
    
END
