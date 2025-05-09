#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <ctype.h>
#include <time.h> // ⏱️ for time tracking

char negate(char lit) {
    return islower(lit) ? toupper(lit) : tolower(lit);
}

int clauseContains(char *clause, char lit) {
    for (int i = 0; clause[i] != '\0'; i++) {
        if (clause[i] == lit) return 1;
    }
    return 0;
}

void printClause(const char *clause) {
    printf("[");
    for (int i = 0; i < strlen(clause); i++) {
        printf("%c", clause[i]);
    }
    printf("]");
}

void dp(int C, char **clauses, int ll) {
    clock_t start = clock(); // ⏱️ start timing

    char **working = malloc(C * sizeof(char *));
    for (int i = 0; i < C; i++) {
        working[i] = strdup(clauses[i]);
    }
    int numClauses = C;

    while (numClauses > 0) {
        bool unitFound = false;
        char lit = '\0';

        for (int i = 0; i < numClauses; i++) {
            if (strlen(working[i]) == 1) {
                lit = working[i][0];
                unitFound = true;
                break;
            }
        }

        if (!unitFound) lit = working[0][0];
        char neg = negate(lit);

        char **newClauses = malloc(numClauses * sizeof(char *));
        int newCount = 0;

        for (int i = 0; i < numClauses; i++) {
            char *clause = working[i];
            if (clauseContains(clause, lit)) {
                printf("Clause ");
                printClause(clause);
                printf(" is satisfied by literal %c. Removing.\n", lit);
                free(clause);
                continue;
            }

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

            free(clause);

            if (k == 0) {
                printf("Derived empty clause. Formula is UNSAT.\n");

                free(newClause);
                for (int x = i + 1; x < numClauses; x++) free(working[x]);
                for (int x = 0; x < newCount; x++) free(newClauses[x]);
                free(newClauses);
                free(working);

                clock_t end = clock(); // ⏱️ stop timing
                double ms = 1000.0 * (end - start) / CLOCKS_PER_SEC;
                printf("Time taken: %.2f ms\n", ms);

                printf("Press Enter to continue...\n");
                getchar(); getchar();
                return;
            }

            newClauses[newCount++] = newClause;
        }

        free(working);
        working = newClauses;
        numClauses = newCount;
    }

    printf("Formula is SAT.\n");
    for (int i = 0; i < numClauses; i++) free(working[i]);
    free(working);

    clock_t end = clock(); // ⏱️ stop timing
    double ms = 1000.0 * (end - start) / CLOCKS_PER_SEC;
    printf("Time taken: %.2f ms\n", ms);

    printf("Press Enter to continue...\n");
    getchar();
}

int main() {
    char *clauses[] = {
        "Ab",
        "AC",
        "bC",
        "aB",
        "Bc",
        "ac"
    };

    int num = sizeof(clauses) / sizeof(clauses[0]);

    dp(num, clauses, 1);
    return 0;
}
