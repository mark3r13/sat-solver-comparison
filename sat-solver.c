#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <ctype.h>
#include <time.h>

int track = 0;

// Clears the terminal screen, depending on the operating system
void clearTerminal() {
    #ifdef _WIN32
        system("cls");  // Windows
    #else
        system("clear"); // Linux/macOS
    #endif
}

// Reads the number of literals for a single clause from the user
void readK(int *K) {
    printf("Enter the number of literals: ");
    scanf("%d", K);
    printf("\n");
}

// Reads multiple clauses from the user and stores them in a dynamically allocated array
// Each clause is represented as a string of characters
void readC(int *C, char ***clauses) {
    printf("Enter the number of clauses: ");
    if (scanf("%d", C) != 1 || *C <= 0) {
        printf("Invalid number of clauses.\n\n");
        while ((getchar()) != '\n'); // Clear input buffer
        return;
    }
    while ((getchar()) != '\n'); // Clear newline

    *clauses = (char **)malloc(*C * sizeof(char *));
    for (int i = 0; i < *C; i++) {
        int K;
        printf("Clause %d:\n", i + 1);
        while (1) {
            printf("  Number of literals: ");
            if (scanf("%d", &K) == 1 && K > 0) break;
            printf("  Invalid input. Must be > 0.\n");
            while ((getchar()) != '\n'); // Clear input buffer
        }
        while ((getchar()) != '\n'); // Clear newline

        (*clauses)[i] = (char *)malloc((K + 1) * sizeof(char));
        for (int j = 0; j < K; j++) {
            printf("    Enter literal %d (a-z or A-Z): ", j + 1);
            char lit;
            if (scanf(" %c", &lit) != 1 || !isalpha(lit)) {
                printf("    Invalid literal. Try again.\n");
                j--; // Repeat input
                while ((getchar()) != '\n'); // Clear input buffer
                continue;
            }
            (*clauses)[i][j] = lit;
        }
        (*clauses)[i][K] = '\0'; // Null-terminate clause
        while ((getchar()) != '\n'); // Clear newline
    }

    clearTerminal();
    printf("Clauses read successfully!\n\n");
}

// Prints all the clauses stored in the dynamically allocated array
// Each clause is displayed with its index for easy reference
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
    getchar(); // Clear buffer
    getchar(); // Wait for enter key press
    clearTerminal();
}

// Displays the main menu options to the user
void showOpts() {
    printf("Options:\n");
    printf("1. Read clauses\n");
    printf("2. Print clauses\n");
    printf("3. Resolution\n");
    printf("4. Davis Putnam\n");
    printf("5. DPLL\n");
    printf("6. Track time"); 
    if(track == 0) printf(" (off)\n");
    else printf(" (on)\n");
    printf("7. Exit\n");
}

// Negates a literal (a <-> A, B <-> b, etc.)
// All literals are assumed to be single characters (a-z, A-Z)
char negate(char lit) {
    return islower(lit) ? toupper(lit) : tolower(lit);
}

// Checks if a clause contains a particular literal
int clauseContains(char *clause, char lit) {
    for(int i = 0; clause[i] != '\0'; i++) {
        if(clause[i] == lit) return 1;
    }
    return 0;
}

// Resolves two clauses based on a literal and returns the resolvent clause
// The resolvent is formed by removing the literal from the first clause and the negation of the literal from the second clause
// and combining the remaining literals
// The function also ensures that no duplicate literals are included in the resolvent
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

// Checks if a clause is new (not already in the list)
int isNewClause(char **resolvents, int count, char *clause) {
    for(int i = 0; i < count; i++) {
        if(strcmp(resolvents[i], clause) == 0) return 0;
    }
    return 1;
}

// Implements the resolution algorithm to try to derive an empty clause
void resolution(int C, char **clauses) {
    char **allClauses = (char **)malloc(1000 * sizeof(char *)); // Arbitrary large space for clauses
    int total = 0;

    // Copy initial clauses to allClauses
    for (int i = 0; i < C; i++) {
        allClauses[total++] = strdup(clauses[i]);
    }

    // Add negated literals to allClauses
    int newDerived = 1;
    while (newDerived) {
        newDerived = 0;

        // Iterate through all pairs of clauses
        for (int i = 0; i < total; i++) {
            for (int j = i + 1; j < total; j++) {
                for (int k = 0; allClauses[i][k] != '\0'; k++) {
                    char lit = allClauses[i][k];
                    char neg = negate(lit);

                    // Check if the negation of the literal exists in the other clause
                    // If it does, resolve the clauses
                    if (clauseContains(allClauses[j], neg)) {
                        char *res = resolveClauses(allClauses[i], allClauses[j], lit);

                        // Check if the resolvent is empty
                        // If it is, the formula is unsatisfiable
                        // and we can exit the loop
                        if (strlen(res) == 0) {
                            printf("Derived empty clause from [%s] and [%s].\n", allClauses[i], allClauses[j]);
                            printf("The formula is UNSAT.\n");
                            free(res);
                            for (int x = 0; x < total; x++) free(allClauses[x]);
                            free(allClauses);
                            return;
                        }

                        // Check if the resolvent is new
                        // If it is, add it to the list of all clauses
                        // and set newDerived to 1
                        // to continue the loop
                        // Otherwise, free the resolvent
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

// Prints a clause with brackets around it
void printClause(const char *clause) {
    printf("[");
    for (int i = 0; i < strlen(clause); i++) {
        printf("%c", clause[i]);
    }
    printf("]");
}

// Checks if the current assignment satisfies all clauses
// Returns 1 if satisfied, 0 otherwise
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

// DPLL algorithm for SAT solving
// It recursively assigns values to variables and checks for satisfiability
// Returns 1 if satisfiable, 0 otherwise
int dpll(char **clauses, int num_clauses, int *assignments, int num_vars) {
    // Check if all clauses are satisfied or if there are no clauses left
    // If all clauses are satisfied, return SAT
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

// Davis-Putnam algorithm for SAT solving
// It uses unit propagation and backtracking to find a satisfying assignment
void dp(int C, char **clauses, int ll) {
    if (clauses == NULL || C <= 0) {
        printf("No clauses provided.\n\n");
        return;
    }

    int maxVars = 26;
    int assignments[maxVars];
    memset(assignments, 0, sizeof(assignments));

    // === DPLL Shortcut Mode ===
    if (ll == 0) {
        if (dpll(clauses, C, assignments, maxVars)) {
            printf("The formula is SAT.\n");
        } else {
            printf("The formula is UNSAT.\n");
        }

        // Pause to view result
        printf("Press Enter to continue...\n");
        while ((getchar()) != '\n' && getchar() != EOF);
        getchar();
        clearTerminal();
        return;
    }

    // === Unit Propagation Mode ===
    char **working = malloc(C * sizeof(char *));
    for (int i = 0; i < C; i++) {
        working[i] = strdup(clauses[i]);
    }
    int numClauses = C;

    while (numClauses > 0) {
        bool unitFound = false;
        char lit = '\0';

        // Find unit clause
        for (int i = 0; i < numClauses; i++) {
            if (strlen(working[i]) == 1) {
                lit = working[i][0];
                unitFound = true;
                break;
            }
        }

        // If no unit clause, pick arbitrary literal
        if (!unitFound) {
            lit = working[0][0];
        }

        char neg = negate(lit);
        char **newClauses = malloc(numClauses * sizeof(char *));
        int newCount = 0;

        for (int i = 0; i < numClauses; i++) {
            char *clause = working[i];

            // Clause is satisfied by literal → discard
            if (clauseContains(clause, lit)) {
                printf("Clause ");
                printClause(clause);
                printf(" is satisfied by literal %c. Removing.\n", lit);
                free(clause);
                continue;
            }

            // Remove negated literal
            int len = strlen(clause);
            char *newClause = malloc(len + 1);
            int k = 0;
            for (int j = 0; j < len; j++) {
                if (clause[j] != neg) {
                    newClause[k++] = clause[j];
                }
            }
            newClause[k] = '\0';

            printf("Simplifying clause ");
            printClause(clause);
            printf(" by removing %c (negation of %c). Result: ", neg, lit);
            printClause(newClause);
            printf("\n");

            free(clause); // free old clause

            // Empty clause → UNSAT
            if (k == 0) {
                printf("Derived empty clause by assigning %c. Conflict found. Formula is UNSAT.\n\n", lit);

                // Cleanup
                free(newClause);
                for (int x = 0; x < newCount; x++) free(newClauses[x]);
                free(newClauses);
                for (int x = i + 1; x < numClauses; x++) free(working[x]);
                free(working);

                printf("Press Enter to continue...\n");
                while ((getchar()) != '\n' && getchar() != EOF);
                getchar();
                clearTerminal();
                return;
            }

            newClauses[newCount++] = newClause;
        }

        free(working);
        working = newClauses;
        numClauses = newCount;
    }

    // If loop completes: SAT
    printf("No conflict found. Formula is SAT.\n\n");
    for (int i = 0; i < numClauses; i++) free(working[i]);
    free(working);

    printf("Press Enter to continue...\n");
    while ((getchar()) != '\n' && getchar() != EOF);
    getchar();
    clearTerminal();
}

int main() {
    clearTerminal();
    printf("Welcome to SAT Resolution!\n\n");

    int C = 0;
    char **clauses = NULL;

    while (1) {
        showOpts();
        int choice;
        printf("Enter your choice: ");
        if (scanf("%d", &choice) != 1) {
            printf("Invalid input. Try again.\n");
            while ((getchar()) != '\n' && getchar() != EOF); // flush input
            continue;
        }
        while ((getchar()) != '\n' && getchar() != EOF); // flush leftover newline

        switch (choice) {
            case 1:
                // Free old clauses if they exist
                if (clauses != NULL) {
                    for (int i = 0; i < C; i++) {
                        free(clauses[i]);
                    }
                    free(clauses);
                    clauses = NULL;
                    C = 0;
                }
                readC(&C, &clauses);
                break;

            case 2:
                if (clauses == NULL || C == 0) {
                    printf("No clauses to print. Please read clauses first.\n\n");
                } else {
                    printC(C, clauses);
                }
                break;

            case 3: // Resolution
                clearTerminal();
                if (clauses == NULL || C == 0) {
                    printf("No clauses to resolve. Please read clauses first.\n\n");
                } else {
                    if (track) {
                        clock_t start = clock();
                        resolution(C, clauses);
                        clock_t end = clock();
                        printf("Time taken: %.2f ms\n",
                            ((double)(end - start)) * 1000 / CLOCKS_PER_SEC);
                    } else {
                        resolution(C, clauses);
                    }
                    printf("Press Enter to continue...\n");
                    while ((getchar()) != '\n' && getchar() != EOF);
                    getchar();
                    clearTerminal();
                }
                break;

            case 4: // Davis-Putnam
                clearTerminal();
                if (clauses == NULL || C == 0) {
                    printf("No clauses to resolve. Please read clauses first.\n\n");
                } else {
                    if (track) {
                        clock_t start = clock();
                        dp(C, clauses, 0);
                        clock_t end = clock();
                        printf("Time taken: %.2f ms\n",
                            ((double)(end - start)) * 1000 / CLOCKS_PER_SEC);
                    } else {
                        dp(C, clauses, 0);
                    }
                    printf("Press Enter to continue...\n");
                    while ((getchar()) != '\n' && getchar() != EOF);
                    getchar();
                    clearTerminal();
                }
                break;

            case 5: // DPLL
                clearTerminal();
                if (clauses == NULL || C == 0) {
                    printf("No clauses to resolve. Please read clauses first.\n\n");
                } else {
                    if (track) {
                        clock_t start = clock();
                        dp(C, clauses, 1);
                        clock_t end = clock();
                        printf("Time taken: %.2f ms\n",
                            ((double)(end - start)) * 1000 / CLOCKS_PER_SEC);
                    } else {
                        dp(C, clauses, 1);
                    }
                    printf("Press Enter to continue...\n");
                    while ((getchar()) != '\n' && getchar() != EOF);
                    getchar();
                    clearTerminal();
                }
                break;

            case 6: // Toggle time tracking
                track = !track;
                clearTerminal();
                break;

            case 7: // Exit
                printf("Exiting...\n");

                // Cleanup memory
                if (clauses != NULL) {
                    for (int i = 0; i < C; i++) {
                        free(clauses[i]);
                    }
                    free(clauses);
                }

                printf("Press Enter to exit...\n");
                while ((getchar()) != '\n' && getchar() != EOF);
                getchar();
                clearTerminal();
                return 0;

            default:
                printf("Invalid choice. Try again.\n\n");
                break;
        }
    }
}