#include <iostream>
#include "cadical.hpp"
#include <map>
#include <iomanip>

#define COUNT_CLAUSES 1
#define NUM_ATTRIBUTES 5

using namespace CaDiCaL;
using namespace std;

Solver solver;

const string nationalites[NUM_ATTRIBUTES] = {"Britannique", "Suedois", "Danois", "Norvegien", "Allemand"};
const string boissons[NUM_ATTRIBUTES] = {"The", "Eau", "Cafe", "Lait", "Biere"};
const string couleurs[NUM_ATTRIBUTES] = {"Rouge", "Bleue", "Jaune", "Verte", "Blanche"};
const string cigarettes[NUM_ATTRIBUTES] = {"Blend", "Prince", "Dunhill", "Bluemaster", "Pall Mall"};
const string animaux[NUM_ATTRIBUTES] = {"Chiens", "Oiseaux", "Chats", "Chevaux", "Poissons"};

const string *arrayPtrs[] = {nationalites, boissons, couleurs, cigarettes, animaux}; // To allow for iterations over our 5 arrays

map<string, vector<int>> var2lit;

int numberOfClauses = 0;

// Add a clause
inline void add( const vector<int> &clause )
{
    #if COUNT_CLAUSES
        numberOfClauses++;
    #endif
    for ( int lit : clause )
    {
        solver . add( lit );
    }
    solver . add( 0 );
}

// Add a single literal
inline void add( const int lit )
{
    #if COUNT_CLAUSES
        if ( lit == 0 ) numberOfClauses++;
    #endif
    solver . add( lit );
}

// Naive implementation of ATMOST1
inline void encode_am1( const vector<int> &clause )
{
    for ( int i = 0; i < clause . size(); i++ )
    {
        for ( int j = i + 1; j < clause . size(); j++ )
        {
            add( {-clause[ i ], -clause[ j ]} );
        }
    }
    for ( int lit : clause )
        add( lit );
    add( 0 );
}

// Get a new lit number
inline int get_new_lit()
{
    static int litNumber;
    return ++litNumber;
}

// A simple double implication ; if lit1 is true, then so is lit2, and if lit2 is true, then so is lit1.
inline void encode_double_implication( int lit1, int lit2 )
{
    add( {lit1, -lit2} );
    add( {-lit1, lit2} );
}

// Creates & assigns 5 lits for each possible attribute (ex. "Lait"). First lit being linked to its presence in the 1st house,
// 2nd lit to its presence in the 2nd house, and so forth.
inline void populate_map( const string vars[NUM_ATTRIBUTES] )
{
    for ( int i = 0; i < NUM_ATTRIBUTES; i++ )
    {
        const auto &var = vars[ i ];
        var2lit[ var ] . resize( NUM_ATTRIBUTES );
        for ( int j = 0; j < NUM_ATTRIBUTES; j++ )
        {
            var2lit[ var ][ j ] = get_new_lit();
        }
        encode_am1( var2lit[ var ] ); // A nationalite/boisson/animal/cigarette/couleur can not be in 2 houses simultaneously
    }
}

inline void assign_vars_to_lits()
{
    for ( const auto array : arrayPtrs )
        populate_map( array );
}

// Encodes that at most 1 attribute of a given type is True in a given house
inline void restrict_var( const string vars[NUM_ATTRIBUTES] )
{
    for ( int i = 0; i < NUM_ATTRIBUTES; i++ )
    {
        encode_am1({var2lit[ vars[ 0 ]][ i ], var2lit[ vars[ 1 ]][ i ], var2lit[ vars[ 2 ]][ i ],
                    var2lit[ vars[ 3 ]][ i ], var2lit[ vars[ 4 ]][ i ]} );
    }
}

inline void encode_at_most_one_per_house()
{
    for ( const auto array : arrayPtrs )
        restrict_var( array );
}

inline int get_house( const string &var )
{
    for ( int i = 0; i < NUM_ATTRIBUTES; i++ )
    {
        if ( solver . val( var2lit[ var ][ i ] ) > 0 )
        {
            return i;
        }
    }
}

// Encodes that if att1 is true, then att2 is true, and vice-versa
inline void encode_linked_attributes( const string &att1, const string &att2 )
{
    for ( int i = 0; i < NUM_ATTRIBUTES; i++ )
    {
        int lit1 = var2lit[ att1 ][ i ];
        int lit2 = var2lit[ att2 ][ i ];
        encode_double_implication( lit1, lit2 );
    }
}

// Encode that att1 is at the immediate left of att2
inline void encode_attribute_left( const string &att1, const string &att2 )
{
    for ( int i = 0; i < NUM_ATTRIBUTES - 1; i++ )
    {
        int lit1 = var2lit[ att1 ][ i ];
        int lit2 = var2lit[ att2 ][ i + 1 ];
        encode_double_implication( lit1, lit2 );
    }
}

// Encodes that att must be located in house number <position>
inline void encode_attribute_forced_position( const string &att, int position )
{
    int lit = var2lit[ att ][ position ];
    add( lit );
    add( 0 );
}

// Encodes that if att2 is at position <k>, then att2 must be at position <k-1> or <k+1>
inline void encode_attribute_between( const string &att1, const string &att2, int position1 )
{
    int lit1 = var2lit[ att1 ][ position1 ];
    int lit2Left = var2lit[ att2 ][ position1 - 1 ];
    int lit2Right = var2lit[ att2 ][ position1 + 1 ];

    add( {-lit2Left, lit1, -lit2Right} );
    add( {lit2Left, -lit1, lit2Right} );
}

// Encodes that if att1 at position1 is True, then att2 must be True at position2
inline void encode_implication( const string &att1, const string &att2, int position1, int position2 )
{
    int lit1 = var2lit[ att1 ][ position1 ];
    int lit2 = var2lit[ att2 ][ position2 ];
    add( {-lit1, lit2} );
}

// Encodes that att1 must be att2's neighbor
inline void encode_attribute_immediate_proximity( const string &att1, const string &att2 )
{
    encode_implication( att1, att2, 0, 1 ); // if att1 @ house_0, then att2 @ house_1
    for ( int i = 1; i < NUM_ATTRIBUTES - 1; i++ )
    {
        encode_attribute_between( att1, att2, i );
    }
    encode_implication( att1, att2, 4, 3 ); // if att1 @ house_4, then att2 @ house_3
}

// Print string with fixed width to make up for a clean table.
inline void print_element( const string &t, int size = 30 )
{
    cout << left << setw( size ) << setfill( ' ' ) << t;
}

// Sorts the "vars" array into the "toPopulate" array in function of the order of the houses.
inline void populate_lit_values_array( const string vars[NUM_ATTRIBUTES], string toPopulate[NUM_ATTRIBUTES] )
{
    for ( int i = 0; i < NUM_ATTRIBUTES; i++ )
        toPopulate[ get_house( vars[ i ] ) ] = vars[ i ];
}

void print_table()
{
    // <!-- Get sorted arrays in function of the houses in which are the attributes -->
    string litsNationalites[NUM_ATTRIBUTES]; populate_lit_values_array( nationalites, litsNationalites );
    string litsAnimaux[NUM_ATTRIBUTES];      populate_lit_values_array( animaux, litsAnimaux );
    string litsBoissons[NUM_ATTRIBUTES];     populate_lit_values_array( boissons, litsBoissons );
    string litsCigarettes[NUM_ATTRIBUTES];   populate_lit_values_array( cigarettes, litsCigarettes );
    string litsCouleurs[NUM_ATTRIBUTES];     populate_lit_values_array( couleurs, litsCouleurs );

    // <!-- Printing the houses -->
    for ( int i = 0; i < 4; i++ ) print_element( "----------------------------------------" );
    print_element( "\n|\n|" );
    for ( int i = 0; i < NUM_ATTRIBUTES; i++ ) print_element( "     _" + std::to_string( i + 1 ) + "_" );
    cout << endl; print_element( "| " );
    for ( int i = 0; i < NUM_ATTRIBUTES; i++ ) print_element( "/\\___\\" );
    cout << endl; print_element( "| " );
    for ( int i = 0; i < NUM_ATTRIBUTES; i++ ) print_element( "|_|\"\"|" );
    cout << endl << "| ";

    // <!-- Printing the table itself -->
    cout << "\n"; print_element( "\033[0m| Couleur\033[0;32m", 41 );
    for ( const string &var : litsCouleurs ) print_element( var );
    cout << "\n"; print_element( "\033[0m| Nationalite\033[0;32m", 41 );
    for ( const string &var : litsNationalites ) print_element( var );
    cout << endl; print_element( "\033[0m| Animal\033[0;32m", 41 );
    for ( const string &var : litsAnimaux ) print_element( var );
    cout << endl; print_element( "\033[0m| Cigarettes\033[0;32m", 41 );
    for ( const string &var : litsCigarettes ) print_element( var );
    cout << endl; print_element( "\033[0m| Boisson\033[0;32m", 41 );
    for ( const string &var : litsBoissons ) print_element( var );
    cout << "\033[0m" << endl;
}

int main()
{
    assign_vars_to_lits();

    encode_at_most_one_per_house();

    // Le britannique vit dans la maison rouge.
    encode_linked_attributes( "Britannique", "Rouge" );

    // Le suédois a des chiens.
    encode_linked_attributes( "Suedois", "Chiens" );

    // Le Danois bois du thé.
    encode_linked_attributes( "Danois", "The" );

    // La maison verte est directement à gauche de la maison blanche.
    encode_attribute_left( "Verte", "Blanche" );

    // Le propriétaire de la maison verte boit du café.
    encode_linked_attributes( "Verte", "Cafe" );

    // La personne qui fume des Pall Mall élève des oiseaux.
    encode_linked_attributes( "Pall Mall", "Oiseaux" );

    // Le propriétaire de la maison jaune fume des Dunhill.
    encode_linked_attributes( "Jaune", "Dunhill" );

    // La personne qui vit dans la maison du centre boit du lait.
    encode_attribute_forced_position( "Lait", 2 );

    // Le Norvégien habite dans la première maison en partant de la gauche.
    encode_attribute_forced_position( "Norvegien", 0 );

    // L’homme qui fume des Blend vit à côté de celui qui a des chats.
    encode_attribute_immediate_proximity( "Blend", "Chats" );

    // L’homme qui a un cheval est le voisin de celui qui fume des Dunhill.
    encode_attribute_immediate_proximity( "Chevaux", "Dunhill" );

    // Celui qui fume des Bluemaster boit de la bière.
    encode_linked_attributes( "Bluemaster", "Biere" );

    // L’Allemand fume des Prince.
    encode_linked_attributes( "Allemand", "Prince" );

    // Le Norvégien vit juste à côté de la maison bleue.
    encode_attribute_immediate_proximity( "Norvegien", "Bleue" );

    // L’homme qui fume des Blend a un voisin qui boit de l’eau.
    encode_attribute_immediate_proximity( "Blend", "Eau" );

    if ( solver . solve() == 10 )
    {
        #if COUNT_CLAUSES
            cout << "\nSATISFIABLE WITH TOTAL OF " << numberOfClauses << " CLAUSES AND " << get_new_lit() - 1 << " LITERALS.\n" << endl;
        #endif
        print_table();
    } else
        cerr << "ERROR : NOT SATISFIABLE ?!" << endl;

    return 0;
}
