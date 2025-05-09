#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <ctype.h>
#include <time.h>

#define MAX_VARS 26

char negate(char lit) {
    return islower(lit) ? toupper(lit) : tolower(lit);
}

bool is_clause_satisfied(const char *clause, int *assignments) {
    for (int i = 0; clause[i] != '\0'; i++) {
        int var = tolower(clause[i]) - 'a';
        if (assignments[var] == 0) continue;
        if (islower(clause[i]) && assignments[var] == 1) return true;
        if (isupper(clause[i]) && assignments[var] == -1) return true;
    }
    return false;
}

bool is_formula_satisfied(char **clauses, int num_clauses, int *assignments) {
    for (int i = 0; i < num_clauses; i++) {
        if (!is_clause_satisfied(clauses[i], assignments)) return false;
    }
    return true;
}

bool dpll(char **clauses, int num_clauses, int *assignments) {
    if (is_formula_satisfied(clauses, num_clauses, assignments)) return true;

    for (int i = 0; i < num_clauses; i++) {
        if (strlen(clauses[i]) == 1) {
            char lit = clauses[i][0];
            int var = tolower(lit) - 'a';
            int val = islower(lit) ? 1 : -1;
            if (assignments[var] != 0 && assignments[var] != val) return false;
            assignments[var] = val;
            bool result = dpll(clauses, num_clauses, assignments);
            assignments[var] = 0;
            return result;
        }
    }

    for (int var = 0; var < MAX_VARS; var++) {
        if (assignments[var] == 0) {
            assignments[var] = 1;
            if (dpll(clauses, num_clauses, assignments)) return true;
            assignments[var] = -1;
            if (dpll(clauses, num_clauses, assignments)) return true;
            assignments[var] = 0;
            return false;
        }
    }

    return false;
}

void run_dpll(char **clauses, int num_clauses) {
    int assignments[MAX_VARS];
    for (int i = 0; i < MAX_VARS; i++) assignments[i] = 0;

    clock_t start = clock();

    bool sat = dpll(clauses, num_clauses, assignments);

    clock_t end = clock();
    double ms = 1000.0 * (end - start) / CLOCKS_PER_SEC;

    printf("\nDPLL result: %s\n", sat ? "SAT" : "UNSAT");
    printf("Time taken: %.2f ms\n", ms);

    if (sat) {
        printf("Satisfying assignment:\n");
        for (int i = 0; i < MAX_VARS; i++) {
            if (assignments[i] == 1) printf("%c = true\n", 'a' + i);
            else if (assignments[i] == -1) printf("%c = false\n", 'a' + i);
        }
    }

    printf("\nPress Enter to continue...\n");
    while ((getchar()) != '\n' && getchar() != EOF);
    getchar();
}

int main() {
    // Dynamically allocated safe input (not string literals)
    char **clauses = malloc(5 * sizeof(char *));
    clauses[0] = strdup("AbC");
    clauses[1] = strdup("BC");
    clauses[2] = strdup("aC");
    clauses[3] = strdup("Bc");
    clauses[4] = strdup("b");

    run_dpll(clauses, 5);

    for (int i = 0; i < 5; i++) {
        free(clauses[i]);
    }
    free(clauses);

    return 0;
}
