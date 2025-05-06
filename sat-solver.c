#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <ctype.h>

void clearTerminal() {
    #ifdef _WIN32
        system("cls");  // Windows
    #else
        system("clear"); // Linux/macOS
    #endif
}

void readK(int *K) {
    printf("Enter the number of literals: ");
    scanf("%d", K);
    printf("\n");
}

void readC(int *C, char ***clauses) {
    printf("Enter the number of clauses: ");
    scanf("%d", C);
    printf("\n");

    *clauses = (char **)malloc(*C * sizeof(char *));
    for(int i = 0; i < *C; i++) {
        int K, j = 0;
        readK(&K);
        (*clauses)[i] = (char *)malloc((K + 1) * sizeof(char));
        for(j = 0; j < K; j++) {
            printf("Enter literal %d for clause %d: ", j + 1, i + 1);
            scanf(" %c", &(*clauses)[i][j]);
        }
        (*clauses)[i][j] = '\0';
        putchar('\n');
    }
    clearTerminal();
    printf("Clauses read successfully!\n\n");
}

void printC(int C, char **clauses) {
    for(int i = 0; i < C; i++) {
        printf("Clause %d: ", i + 1);
        for(int j = 0; clauses[i][j] != '\0'; j++) {
            printf("%c ", clauses[i][j]);
        }
        printf("\n");
    }
    putchar('\n');
    printf("Press Enter to continue...\n");
    getchar();
    getchar();
    clearTerminal();
}

void showOpts() {
    printf("Options:\n");
    printf("1. Read clauses\n");
    printf("2. Print clauses\n");
    printf("3. Resolution\n");
    printf("4. Davis Putnam\n");
    printf("5. DPLL\n");
    printf("6. Exit\n");
}

char negate(char lit) {
    return islower(lit) ? toupper(lit) : tolower(lit);
}

int clauseContains(char *clause, char lit) {
    for(int i = 0; clause[i] != '\0'; i++) {
        if(clause[i] == lit) return 1;
    }
    return 0;
}

char *resolveClauses(char *clause1, char *clause2, char lit) {
    int len1 = strlen(clause1), len2 = strlen(clause2);
    char *resolvent = (char *)malloc(len1 + len2 + 1);
    int k = 0;

    for(int i = 0; i < len1; i++) {
        if(clause1[i] != lit) resolvent[k++] = clause1[i];
    }

    for(int i = 0; i < len2; i++) {
        if(clause2[i] != negate(lit) && !clauseContains(resolvent, clause2[i])) {
            resolvent[k++] = clause2[i];
        }
    }

    resolvent[k] = '\0';
    return resolvent;
}

int isNewClause(char **resolvents, int count, char *clause) {
    for(int i = 0; i < count; i++) {
        if(strcmp(resolvents[i], clause) == 0) return 0;
    }
    return 1;
}

void resolution(int C, char **clauses) {
    char **allClauses = (char **)malloc(1000 * sizeof(char *));
    int total = 0;

    for (int i = 0; i < C; i++) {
        allClauses[total++] = strdup(clauses[i]);
    }

    int newDerived = 1;
    while (newDerived) {
        newDerived = 0;

        for (int i = 0; i < total; i++) {
            for (int j = i + 1; j < total; j++) {
                for (int k = 0; allClauses[i][k] != '\0'; k++) {
                    char lit = allClauses[i][k];
                    char neg = negate(lit);

                    if (clauseContains(allClauses[j], neg)) {
                        char *res = resolveClauses(allClauses[i], allClauses[j], lit);

                        if (strlen(res) == 0) {
                            printf("Derived empty clause from [%s] and [%s].\n", allClauses[i], allClauses[j]);
                            printf("The formula is UNSAT.\n");
                            free(res);
                            for (int x = 0; x < total; x++) free(allClauses[x]);
                            free(allClauses);
                            return;
                        }

                        if (isNewClause(allClauses, total, res)) {
                            printf("New clause from [%s] and [%s]: %s\n", allClauses[i], allClauses[j], res);
                            allClauses[total++] = res;
                            newDerived = 1;
                        } else {
                            free(res);
                        }
                    }
                }
            }
        }
    }

    printf("\nNo empty clause found after saturation. The formula is possibly SAT.\n");

    for (int i = 0; i < total; i++) free(allClauses[i]);
    free(allClauses);

    printf("Press Enter to continue...\n");
    getchar();
    getchar();
    clearTerminal();
}

void printClause(const char *clause) {
    printf("[");
    for (int i = 0; i < strlen(clause); i++) {
        printf("%c", clause[i]);
    }
    printf("]");
}

int is_satisfied(char **clauses, int num_clauses, int *assignments, int num_vars) {
    for (int i = 0; i < num_clauses; i++) {
        int satisfied = 0;
        for (int j = 0; clauses[i][j] != '\0'; j++) {
            int var = tolower(clauses[i][j]) - 'a';
            int val = (assignments[var] == 1) ? 1 : 0;
            if ((clauses[i][j] == tolower(clauses[i][j]) && val == 1) || 
                (clauses[i][j] != tolower(clauses[i][j]) && val == 0)) {
                satisfied = 1;
                break;
            }
        }
        if (!satisfied) return 0;
    }
    return 1;
}

int dpll(char **clauses, int num_clauses, int *assignments, int num_vars) {
    if (is_satisfied(clauses, num_clauses, assignments, num_vars)) {
        return 1; // SAT
    }
    if (num_clauses == 0) {
        return 1; // No clauses left to satisfy, SAT
    }

    // Unit propagation
    for (int i = 0; i < num_clauses; i++) {
        if (strlen(clauses[i]) == 1) { // Unit clause
            char literal = clauses[i][0];
            int var = tolower(literal) - 'a';
            assignments[var] = (literal == tolower(literal)) ? 1 : -1;
            return dpll(clauses, num_clauses, assignments, num_vars);
        }
    }

    // Choosing a literal and trying both true and false
    for (int i = 0; i < num_vars; i++) {
        if (assignments[i] == 0) { // If unassigned
            assignments[i] = 1;
            if (dpll(clauses, num_clauses, assignments, num_vars)) {
                return 1; // SAT
            }
            assignments[i] = -1;
            if (dpll(clauses, num_clauses, assignments, num_vars)) {
                return 1; // SAT
            }
            assignments[i] = 0; // Backtrack
            return 0; // UNSAT
        }
    }
    return 0; // UNSAT
}

void dp(int C, char **clauses, int ll) {
    int maxVars = 26;
    int assignments[maxVars];
    memset(assignments, 0, sizeof(assignments));

    // Check for DPLL if ll is set to 0
    if (ll == 0) {
        if (dpll(clauses, C, assignments, maxVars)) {
            printf("The formula is SAT.\n");
        } else {
            printf("The formula is UNSAT.\n");
        }
    }

    // Unit propagation resolution (existing algorithm)
    char **working = (char **)malloc(C * sizeof(char *));
    for (int i = 0; i < C; i++) {
        working[i] = strdup(clauses[i]);
    }
    int numClauses = C;

    while (numClauses > 0) {
        bool unitFound = false;
        char lit = '\0';

        // Unit clause detection
        for (int i = 0; i < numClauses; i++) {
            if (strlen(working[i]) == 1) {
                lit = working[i][0];
                unitFound = true;
                break;
            }
        }

        // If no unit, pick first literal of first clause
        if (!unitFound && numClauses > 0) {
            lit = working[0][0];
        }

        char neg = negate(lit);

        // Simplify clauses
        char **newClauses = (char **)malloc(numClauses * sizeof(char *));
        int newCount = 0;

        for (int i = 0; i < numClauses; i++) {
            if (clauseContains(working[i], lit)) {
                // Clause satisfied by current literal, discard it
                printf("Clause ");
                printClause(working[i]);
                printf(" is satisfied by literal %c. Removing.\n", lit);
                free(working[i]);
                continue;
            }

            int len = strlen(working[i]);
            char *newClause = (char *)malloc(len + 1);
            int k = 0;
            for (int j = 0; j < len; j++) {
                if (working[i][j] != neg) {
                    newClause[k++] = working[i][j];
                }
            }
            newClause[k] = '\0';

            printf("Simplifying clause ");
            printClause(working[i]);
            printf(" by removing %c (negation of %c). Result: ", neg, lit);
            printClause(newClause);
            printf("\n");

            if (k == 0) {
                printf("Derived empty clause from ");
                printClause(working[i]);
                printf(" by assigning %c. Conflict found. Formula is UNSAT.\n\n", lit);
                for (int x = 0; x < newCount; x++) free(newClauses[x]);
                free(newClauses);
                for (int x = 0; x < numClauses; x++) free(working[x]);
                free(working);
                return;
            }

            newClauses[newCount++] = newClause;
            free(working[i]);
        }

        free(working);
        working = newClauses;
        numClauses = newCount;
    }

    printf("No conflict found. Formula is SAT.\n\n");
    for (int i = 0; i < numClauses; i++) free(working[i]);
    free(working);

    printf("Press Enter to continue...\n");
    getchar();
    getchar();
    clearTerminal();
}

int main() {
    clearTerminal();
    printf("Welcome to SAT Resolution!\n\n");
    int C;
    char **clauses;

    while(1) {
        showOpts();
        int choice;
        printf("Enter your choice: ");
        scanf("%d", &choice);
        putchar('\n');

        switch(choice) {
            case 1:
                readC(&C, &clauses);
                break;
            case 2:
                printC(C, clauses);
                break;
            case 3:
                clearTerminal();
                if(C == 0) {
                    printf("No clauses to resolve. Please read clauses first.\n\n");
                } else {
                    resolution(C, clauses);
                }
                break;
            case 4:
                clearTerminal();
                if(C == 0) {
                    printf("No clauses to resolve. Please read clauses first.\n\n");
                } else {
                    dp(C, clauses, 0);
                }
                break;
            case 5:
                clearTerminal();
                if(C == 0) {
                    printf("No clauses to resolve. Please read clauses first.\n\n");
                } else {
                    dp(C, clauses, 1);
                }
                break;
            case 6:
                printf("Exiting...\n");
                getchar();
                getchar();
                clearTerminal();
                exit(0);
                break;
            default:
                printf("Invalid choice. Please try again.\n\n");
                break;
        }
    }

    printf("FLAG\n");

    // Free allocated memory
    for(int i = 0; i < C; i++) {
        free(clauses[i]);
    }
    free(clauses);
    printf("Memory cleared succesfully!\n");
    getchar();
    clearTerminal();

    printf("Exiting...\n");
    return 0;
}