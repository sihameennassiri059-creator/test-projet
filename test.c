#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>


#define MAXETATS       100
#define MAXALPHABET    26
#define MAXTRANSITIONS 500

typedef struct {
    int  etatdepart;
    char symbole;       
    int  etatarrivee;
} Transition;

typedef enum {
    NON_DETERMINISTE,
    DETERMINISTE
} TypeAutomate;

typedef struct {

    TypeAutomate type;

    int  nbetats;
    int  etats[MAXETATS];

    int  nbsymboles;
    char alphabet[MAXALPHABET];

    int  nbtransitions;
    Transition transitions[MAXTRANSITIONS];

    int  nbetatsinitiaux;
    int  etatsinitiaux[MAXETATS];

    int  nbetatsfinaux;
    int  etatsfinaux[MAXETATS];
} Automate;

/* ================= INITIALISATION ================= */
void initialiser_automate(Automate *A) {
    A->nbetats            = 0;
    A->nbsymboles         = 0;
    A->nbetatsinitiaux   = 0;
    A->nbetatsfinaux     = 0;
    A->nbtransitions      = 0;
}

/* ================= UTILITAIRES ================= */
int existeetat(Automate *A, int etat) {
    for (int i = 0; i < A->nbetats; i++)
        if (A->etats[i] == etat) return 1;
    return 0;
}

int existesymbole(Automate *A, char symbole) {
    for (int i = 0; i < A->nbsymboles; i++)
        if (A->alphabet[i] == symbole) return 1;
    return 0;
}

int estfinal(Automate *A, int etat) {
    for (int i = 0; i < A->nbetatsfinaux; i++)
        if (A->etatsfinaux[i] == etat) return 1;
    return 0;
}

int estinitial(Automate *A, int etat) {
    for (int i = 0; i < A->nbetatsinitiaux; i++)
        if (A->etatsinitiaux[i] == etat) return 1;
    return 0;
}

void ajouteretat(Automate *A, int etat) {
    if (!existeetat(A, etat) && A->nbetats < MAXETATS)
        A->etats[A->nbetats++] = etat;
}

void ajoutersymbole(Automate *A, char symbole) {
    if (!existesymbole(A, symbole) && A->nbsymboles < MAXALPHABET)
        A->alphabet[A->nbsymboles++] = symbole;
}

void ajouteretatinitial(Automate *A, int etat) {
    if (!existeetat(A, etat)) return;
    for (int i = 0; i < A->nbetatsinitiaux; i++)
        if (A->etatsinitiaux[i] == etat) return;
    if (A->nbetatsinitiaux < MAXETATS)
        A->etatsinitiaux[A->nbetatsinitiaux++] = etat;
}

void ajouteretatfinal(Automate *A, int etat) {
    if (!existeetat(A, etat)) return;
    for (int i = 0; i < A->nbetatsfinaux; i++)
        if (A->etatsfinaux[i] == etat) return;
    if (A->nbetatsfinaux < MAXETATS)
        A->etatsfinaux[A->nbetatsfinaux++] = etat;
}

void ajoutertransition(Automate *A, int dep, char sym, int arr) {
    if (!existeetat(A, dep) || !existeetat(A, arr)) return;
    if (sym != '\0' && !existesymbole(A, sym)) return;
    if (A->nbtransitions >= MAXTRANSITIONS) return;
    A->transitions[A->nbtransitions].etatdepart  = dep;
    A->transitions[A->nbtransitions].symbole      = sym;
    A->transitions[A->nbtransitions].etatarrivee = arr;
    A->nbtransitions++;
}

TypeAutomate detectertype(Automate *A) {
    if (A->nbetatsinitiaux != 1)
        return NON_DETERMINISTE;
    for (int i = 0; i < A->nbtransitions; i++)
        if (A->transitions[i].symbole == '\0')
            return NON_DETERMINISTE;
    for (int i = 0; i < A->nbtransitions; i++)
        for (int j = i+1; j < A->nbtransitions; j++)
            if (A->transitions[i].etatdepart == A->transitions[j].etatdepart &&
                A->transitions[i].symbole    == A->transitions[j].symbole)
                return NON_DETERMINISTE;
    return DETERMINISTE;
}

void lire_dot(Automate *A, const char *ficher) {
    FILE *f = fopen(ficher, "r");
    if (!f) {
        printf("Erreur ouverture fichier %s\n", ficher);
        return;
    }

    initialiser_automate(A);
    char ligne[256];

    while (fgets(ligne, sizeof(ligne), f)) {

        char nomsrc[20], nomdst[20], sym[10];
        int src, dst;

        // --- État initial :  init -> z0;
        if (sscanf(ligne, " init -> z%d ", &src) == 1) {
            ajouteretat(A, src);
            ajouteretatinitial(A, src);
        }

        // --- Transition :  z0 -> z1 [label="a"];
        else if (sscanf(ligne, " z%d -> z%d [label=\"%[^\"]\"];",
                        &src, &dst, sym) == 3) {
            ajouteretat(A, src);
            ajouteretat(A, dst);
            char s = sym[0];
            ajoutersymbole(A, s);
            ajoutertransition(A, src, s, dst);
        }

        // --- États finaux :  node [shape=doublecircle]; z3; z4;
        //     OU bien :       z3[shape=doublecircle];
        else if (strstr(ligne, "doublecircle")) { //strstr:cherche doublecircle dans la ligne
            int ef;
            // Cas : z3[shape=doublecircle];
            if (sscanf(ligne, " z%d [shape=doublecircle];", &ef) == 1) {
                ajouteretat(A, ef);
                ajouteretatfinal(A, ef);
            }
            // Cas : node [shape=doublecircle]; z3; z4;
            else {
                char *p = strchr(ligne, ';');//strchr cherche le premier ; dans la ligne et retourne un pointeur vers ce ;
                if (p) {//si on trouve un ; alors on avance le pointeur de 1 pour se placer après le ;
                    p++;
                    char *token = strtok(p, " ;\n");//strtok découpe la chaîne à partir du pointeur p en utilisant les délimiteurs " ;\n" 
                    while (token) {//tant que token n'est pas NULL
                        if (sscanf(token, "z%d", &ef) == 1) {//sscanf lit le token et extrait le numéro d'état ef
                            ajouteretat(A, ef);
                            ajouteretatfinal(A, ef);
                        }
                        token = strtok(NULL, " ;\n");//strtok(NULL, " ;\n") continue à découper la chaîne à partir de la position précédente jusqu'à ce qu'il n'y ait plus de tokens
                    }
                }
            }
        }
    }

    // Détecter automatiquement AFD ou AFN
    A->type = detectertype(A);

    fclose(f);
    printf("Automate charge depuis '%s'\n", ficher);
    printf("Type : %s\n", A->type == DETERMINISTE ?
           "DETERMINISTE" : "NON DETERMINISTE");
}



void afficherautomate(Automate *A) {
    printf("\n===== AUTOMATE (%s) =====\n",
           A->type == DETERMINISTE ? "AFD" : "AFN");

    printf("Etats      : ");
    for (int i = 0; i < A->nbetats; i++) {
        printf("z%d", A->etats[i]);
   
        printf(" ");
    }

    printf("\nAlphabet   : ");
    for (int i = 0; i < A->nbsymboles; i++)
        printf("%c ", A->alphabet[i]);

    printf("\nInitiaux   : ");
    for (int i = 0; i < A->nbetatsinitiaux; i++)
        printf("z%d ", A->etatsinitiaux[i]);

    printf("\nFinaux     : ");
    for (int i = 0; i < A->nbetatsfinaux; i++)
        printf("z%d ", A->etatsfinaux[i]);

    printf("\nTransitions:\n");
    for (int i = 0; i < A->nbtransitions; i++)
        printf("  z%d --%c--> z%d\n",
               A->transitions[i].etatdepart,
               A->transitions[i].symbole,
               A->transitions[i].etatarrivee);
    printf("=========================\n");
}

void genererDot(Automate *A, const char* fichier) {
    FILE *f = fopen(fichier, "w");
    
    if (f == NULL) {
        printf("Erreur ouverture fichier %s\n", fichier);
        return;
    }

    fprintf(f, "digraph Automate {\n");
    fprintf(f, "rankdir=LR;\n");

    // Etats finaux
    fprintf(f, "    node [shape=doublecircle]; ");
    for (int i = 0; i < A->nbetatsfinaux; i++)
        fprintf(f, "z%d; ", A->etatsfinaux[i]);
    fprintf(f, "\n    node [shape=circle];\n\n");


    // État(s) initial/initiaux
    fprintf(f, "    init[shape=point];\n");
    for (int i = 0; i < A->nbetatsinitiaux; i++)
        fprintf(f, "    init -> z%d;\n", A->etatsinitiaux[i]);
    fprintf(f, "\n");

    // Transitions
    for (int i = 0; i < A->nbtransitions; i++)
        fprintf(f, "    z%d -> z%d [label=\"%c\"];\n",
                A->transitions[i].etatdepart,
                A->transitions[i].etatarrivee,
                A->transitions[i].symbole);

    fprintf(f, "}\n");
    fclose(f);
    printf("Automate sauvegarde dans '%s'\n", fichier);
}




void afficher_etat_max_transitions(Automate *A) {
    if (A->nbetats == 0) {
        printf("Aucun etat dans l'automate !\n");
        return;
    }

    int max_sortantes = 0, max_entrantes = 0;
    int etat_max_sortantes = A->etats[0], etat_max_entrantes = A->etats[0];

    for (int i = 0; i < A->nbetats; i++) {
        int e = A->etats[i];
        int nb_sort = 0, nb_ent = 0;

        // Compter transitions sortantes et entrantes
        for (int j = 0; j < A->nbtransitions; j++) {
            if (A->transitions[j].etatdepart == e) nb_sort++;
            if (A->transitions[j].etatarrivee == e) nb_ent++;
        }

        if (nb_sort > max_sortantes) {
            max_sortantes = nb_sort;
            etat_max_sortantes = e;
        }
        if (nb_ent > max_entrantes) {
            max_entrantes = nb_ent;
            etat_max_entrantes = e;
        }
    }

    printf("Etat avec le plus de transitions sortantes : z%d (%d)\n", etat_max_sortantes, max_sortantes);
    printf("Etat avec le plus de transitions entrantes  : z%d (%d)\n", etat_max_entrantes, max_entrantes);
}

//question 7

void afficher_etats_transition_lettre(Automate *A, char lettre) {

    if (A->nbetats == 0) {
        printf("Aucun automate charge !\n");
        return;
    }

    printf("Etats ayant au moins une transition sortante etiquetee par '%c' :\n", lettre);

    int trouve = 0;

    for (int i = 0; i < A->nbetats; i++) {

        int etat = A->etats[i];

        for (int j = 0; j < A->nbtransitions; j++) {

            if (A->transitions[j].etatdepart == etat &&
                A->transitions[j].symbole == lettre) {

                printf("z%d\n", etat);
                trouve = 1;
                break;  // éviter d'afficher le même état plusieurs fois
            }
        }
    }

    if (!trouve)
        printf("Aucun etat ne possede une transition avec cette lettre.\n");
}


//question 8

bool mot_accepte_rec(Automate *A, int etat_courant, const char *mot, int pos) {
    if (mot[pos] == '\0' && estfinal(A, etat_courant)) 
        return true;

    for (int i = 0; i < A->nbtransitions; i++) {
        if (A->transitions[i].etatdepart == etat_courant) {
            char symbole = A->transitions[i].symbole;

            if (symbole == '\0') {
                // epsilon : ne consomme pas de lettre
                if (mot_accepte_rec(A, A->transitions[i].etatarrivee, mot, pos))
                    return true;
            } else if (mot[pos] == symbole) {
                // lettre correspond → avancer
                if (mot_accepte_rec(A, A->transitions[i].etatarrivee, mot, pos + 1))
                    return true;
            }
        }
    }
    return false;
}

int tester_mot(Automate *A, const char *mot) {
    for (int i = 0; i < A->nbetatsinitiaux; i++) {
        if (mot_accepte_rec(A, A->etatsinitiaux[i], mot, 0))
            return 1; // mot accepté
    }
    return 0; // mot rejeté
}

void lire_et_tester_mot(Automate *A) {
    if (A->nbetats == 0) {
        printf("Aucun automate charge !\n");
        return;
    }

    char mot[100];
    printf("Entrez le mot a tester : ");
    scanf("%s", mot);

    if (tester_mot(A, mot))
        printf("Le mot '%s' est accepte par l'automate.\n", mot);
    else
        printf("Le mot '%s' n'est pas accepte par l'automate.\n", mot);
}


// questionn 9

void filtrer_mots_accepter(Automate *A, const char *fichier_entree) {
    if (A->nbetats == 0) {
        printf("Aucun automate charge !\n");
        return;
    }

    FILE *fe = fopen(fichier_entree, "r");
    if (!fe) {
        printf("Erreur ouverture fichier %s\n", fichier_entree);
        return;
    }

    FILE *fs = fopen("MotsAccepter.txt", "w");
    if (!fs) {
        printf("Erreur creation fichier MotsAccepter.txt\n");
        fclose(fe);
        return;
    }

    char mot[100];
    int nb_acceptes = 0;

    while (fgets(mot, sizeof(mot), fe)) {
        // Supprimer le \n final si présent
        mot[strcspn(mot, "\n")] = '\0';

        if (strlen(mot) == 0) continue; // ignorer lignes vides

        if (tester_mot(A, mot)) {
            fprintf(fs, "%s\n", mot);
            nb_acceptes++;
        }
    }

    printf("%d mot(s) accepte(s) ecrit(s) dans MotsAccepter.txt\n", nb_acceptes);

    fclose(fe);
    fclose(fs);
}


// main menu

void menu() {
    Automate A;
    initialiser_automate(&A);
    int choix;
    char fichier[100];

    do {
        printf("\n===== MENU =====\n");
        printf("1. Charger automate (.dot)\n");
        printf("2. Afficher automate\n");
        printf("3. Afficher etats avec max transitions\n");
        printf("4. Generer fichier .dot\n");
        printf("5. Afficher etats avec transition lettre\n");
        printf("6. Tester un mot sur l'automate\n");
        printf("7. Filtrer mots acceptes depuis fichier\n");
        printf("0. Quitter\n");
        printf("Votre choix : ");
        scanf("%d", &choix);

        switch (choix) {
            case 1:
                printf("Nom du fichier .dot : ");
                scanf("%s", fichier);
                lire_dot(&A, fichier);
                break;
            case 2:
                if (A.nbetats == 0)
                    printf("Aucun automate charge !\n");
                else
                    afficherautomate(&A);
                break;

        
            case 3:
                  if (A.nbetats == 0)
                   printf("Aucun automate charge !\n");
                 else
                 afficher_etat_max_transitions(&A);
                break;
            case 4:
                if (A.nbetats == 0)
                    printf("Aucun automate charge !\n");
                else
                    genererDot(&A, "automate.dot");
                break;
            case 5: {
                  char lettre;
                   printf("Donner la lettre : ");
                  scanf(" %c", &lettre);
                  afficher_etats_transition_lettre(&A, lettre);
                 break;
               }
            case 6:
                lire_et_tester_mot(&A);
             break;


             case 7: {
              char fichier_txt[100];
             printf("Nom du fichier .txt : ");
             scanf("%s", fichier_txt);
             filtrer_mots_accepter(&A, fichier_txt);
             break;
     }

            case 0:
                printf("Au revoir!\n");
                break;
            default:
                printf("Choix invalide !\n");
        }
    } while (choix != 0);
}

int main() {
    menu();
    return 0;
}