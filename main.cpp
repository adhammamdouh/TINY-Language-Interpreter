#include <cstdio>
#include <cstdlib>
#include <cstring>
using namespace std;

/*
{ Sample program
  in TINY language
}

int regularInt;                             { initialize variable "regularInt" of type Int }
{ int regularInt; }                         { this will fail if uncommented "ERROR the variable declared before" }
bool regularBool;                           { initialize variable "regularBool" of type Bool }
real regularReal;                           { initialize variable "regularReal" of type Real }
int ctr;                                    { initialize variable "ctr" }
int result;                                 { increase result by 1 }
int sum;                                    { initialize variable "sum" of type Int }
int sub;                                    { initialize variable "sub" of type Int }
real mult;                                  { initialize variable "mult" of type real }
real divide;                                { initialize variable "divide" of type real }

regularInt := 5;                            { set 5 to regularInt }
regularBool := false;                       { set false to regularBool }
regularReal := 6.5;                         { set 6.5 to regularReal }
sum := 10 + 50;                             { set (10 + 50 ) to sum }
sub := regularInt - 4;                      { set (regularInt - 4) to sub }
mult := ( 2.0 * regularReal ) * 10.6;       { set (( 2.0 * regularReal ) * 10.6) to mult }
divide := regularReal / 2.0;                { set (regularReal / 2.0) to divide }

write regularInt;                           { print regularInt "this will print Val: 5" }
write regularBool;                          { print regularBool "this will print Val: 0" }
write regularReal;                          { print regularReal "this will print Val: 6.5" }
write sum;                                  { print sum "this will print Val: 60" }
write sub;                                  { print sub "this will print Val: 1" }
write mult;                                 { print mult "this will print Val: 137.8" }
write divide;                               { print divide "this will print Val: 3.25" }

{ write regularInt + regularReal; }         { this will fail if uncommented "operation among different data types" }
{ write regularInt + regularBool; }         { this will fail if uncommented "operation among different data types" }
{ write regularReal + regularBool; }        { this will fail if uncommented "operation among different data types" }

{ int regularInt; }                         { this will fail if uncommented "you must declare your variables at the beginning of the program" }
{ undeclaredVariable := 12; }               { this will fail if uncommented "ERROR VARIABLES must be declared before use!" }

ctr := 10;                                  { set 10 to ctr }
if 0<ctr then                               { compute only if ctr>=1 }
  result := ctr;                            { set result = ctr }
  repeat                                    { start repeat statement }
    result := result + 1;                   { increase result by 1 }
    write result;                           { write result "this will print Values from 11 to 20" }
    ctr:=ctr-1                              { decrease ctr by 1 }
  until ctr=0                               { end repeat }
end                                         { end program }

*/

// sequence of statements separated by ;
// no procedures - no declarations
// all variables are integers
// variables are declared simply by assigning values to them :=
// if-statement: if (boolean) then [else] end
// repeat-statement: repeat until (boolean)
// boolean only in if and repeat conditions < = and two mathematical expressions
// math expressions integers only, + - * / ^
// I/O read write
// Comments {}

////////////////////////////////////////////////////////////////////////////////////
// Strings /////////////////////////////////////////////////////////////////////////

bool Equals(const char* a, const char* b)
{
    return strcmp(a, b) == 0;
}

bool StartsWith(const char* a, const char* b)
{
    int nb = strlen(b);
    return strncmp(a, b, nb) == 0;
}

void Copy(char* a, const char* b, int n = 0)
{
    if (n > 0) { strncpy(a, b, n); a[n] = 0; }
    else strcpy(a, b);
}

void AllocateAndCopy(char** a, const char* b)
{
    if (b == 0) { *a = 0; return; }
    int n = strlen(b);
    *a = new char[n + 1];
    strcpy(*a, b);
}

////////////////////////////////////////////////////////////////////////////////////
// Input and Output ////////////////////////////////////////////////////////////////

#define MAX_LINE_LENGTH 10000

struct InFile
{
    FILE* file;
    int cur_line_num;

    char line_buf[MAX_LINE_LENGTH];
    int cur_ind, cur_line_size;

    InFile(const char* str) { file = 0; if (str) file = fopen(str, "r"); cur_line_size = 0; cur_ind = 0; cur_line_num = 0; }
    ~InFile() { if (file) fclose(file); }

    void SkipSpaces()
    {
        while (cur_ind < cur_line_size)
        {
            char ch = line_buf[cur_ind];
            if (ch != ' ' && ch != '\t' && ch != '\r' && ch != '\n') break;
            cur_ind++;
        }
    }

    bool SkipUpto(const char* str)
    {
        while (true)
        {
            SkipSpaces();
            while (cur_ind >= cur_line_size) { if (!GetNewLine()) return false; SkipSpaces(); }

            if (StartsWith(&line_buf[cur_ind], str))
            {
                cur_ind += strlen(str);
                return true;
            }
            cur_ind++;
        }
        return false;
    }

    bool GetNewLine()
    {
        cur_ind = 0; line_buf[0] = 0;
        if (!fgets(line_buf, MAX_LINE_LENGTH, file)) return false;
        cur_line_size = strlen(line_buf);
        if (cur_line_size == 0) return false; // End of file
        cur_line_num++;
        return true;
    }

    char* GetNextTokenStr()
    {
        SkipSpaces();
        while (cur_ind >= cur_line_size) { if (!GetNewLine()) return 0; SkipSpaces(); }
        return &line_buf[cur_ind];
    }

    void Advance(int num)
    {
        cur_ind += num;
    }
};

struct OutFile
{
    FILE* file;
    OutFile(const char* str) { file = 0; if (str) file = fopen(str, "w"); }
    ~OutFile() { if (file) fclose(file); }

    void Out(const char* s)
    {
        fprintf(file, "%s\n", s); fflush(file);
    }
};

////////////////////////////////////////////////////////////////////////////////////
// Compiler Parameters /////////////////////////////////////////////////////////////

struct CompilerInfo
{
    InFile in_file;
    OutFile out_file;
    OutFile debug_file;

    CompilerInfo(const char* in_str, const char* out_str, const char* debug_str)
        : in_file(in_str), out_file(out_str), debug_file(debug_str)
    {
    }
};

////////////////////////////////////////////////////////////////////////////////////
// Scanner /////////////////////////////////////////////////////////////////////////

#define MAX_TOKEN_LEN 40

enum TokenType {
    IF, THEN, ELSE, END, REPEAT, UNTIL, READ, WRITE,
    INT, BOOL, REAL, TRUE, FALSE, ASSIGN, EQUAL, LESS_THAN,                 // defined INT, BOOL, REAL, TRUE and False.
    ABSDIFF,                                                                // defined ABSDIFF Token
    PLUS, MINUS, TIMES, DIVIDE, POWER,
    SEMI_COLON,
    LEFT_PAREN, RIGHT_PAREN,
    LEFT_BRACE, RIGHT_BRACE,
    ID,                                                                     // removed num Token
    ENDFILE, ERROR,
};

// Used for debugging only /////////////////////////////////////////////////////////
const char* TokenTypeStr[] =
{
    "If", "Then", "Else", "End", "Repeat", "Until", "Read", "Write",
    "Int", "Bool", "Real", "True", "False", "Assign", "Equal", "LessThan",  // defined Int, Bool, Real, True, False Strings.
    "AbsDiff",                                                              // defined AbsDiff String
    "Plus", "Minus", "Times", "Divide", "Power",
    "SemiColon",
    "LeftParen", "RightParen",
    "LeftBrace", "RightBrace",
    "ID",                                                                   // removed num String
    "EndFile", "Error"
};

struct Token
{
    TokenType type;
    char str[MAX_TOKEN_LEN + 1];

    Token() { str[0] = 0; type = ERROR; }
    Token(TokenType _type, const char* _str) { type = _type; Copy(str, _str); }
};

const Token reserved_words[] =
{
    Token(IF, "if"),
    Token(THEN, "then"),
    Token(ELSE, "else"),
    Token(END, "end"),
    Token(REPEAT, "repeat"),
    Token(UNTIL, "until"),
    Token(INT, "int"),              // defined int as a reserved word.
    Token(BOOL, "bool"),            // defined bool as a reserved word.
    Token(REAL, "real"),            // defined real as a reserved word.
    Token(TRUE, "true"),            // defined true as a reserved word.
    Token(FALSE, "false"),          // defined false as a reserved word.
    Token(READ, "read"),
    Token(WRITE, "write")
};
const int num_reserved_words = sizeof(reserved_words) / sizeof(reserved_words[0]);

// if there is tokens like < <=, sort them such that sub-tokens come last: <= <
// the closing comment should come immediately after opening comment
const Token symbolic_tokens[] =
{
    Token(ASSIGN, ":="),
    Token(EQUAL, "="),
    Token(LESS_THAN, "<"),
    Token(PLUS, "+"),
    Token(MINUS, "-"),
    Token(ABSDIFF, "&"),            // defined & as a symbolic token.
    Token(TIMES, "*"),
    Token(DIVIDE, "/"),
    Token(POWER, "^"),
    Token(SEMI_COLON, ";"),
    Token(LEFT_PAREN, "("),
    Token(RIGHT_PAREN, ")"),
    Token(LEFT_BRACE, "{"),
    Token(RIGHT_BRACE, "}")
};
const int num_symbolic_tokens = sizeof(symbolic_tokens) / sizeof(symbolic_tokens[0]);

inline bool IsDoubleOrInteger(char ch, bool* foundDot)           // modified IsDigit function to check for dots and digits, and renamed to IsDoubleOrInteger
{
    if (ch == '.' && *foundDot) { printf("ERROR No REAL NUMBER contains more than one \".\"\n"); throw 0;}    // if found dot before return false no double with more than one dot.
    if (ch == '.') { *foundDot = true; return true; }                                                         // if ch is '.' then mark set foundDot with true and return true.
    else if (ch >= '0' && ch <= '9') return true;                                                             // if ch is Integer then return true.
    return false;
}
inline bool IsLetter(char ch) { return ((ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z')); }
inline bool IsLetterOrUnderscore(char ch) { return (IsLetter(ch) || ch == '_'); }

void GetNextToken(CompilerInfo* pci, Token* ptoken)
{
    ptoken->type = ERROR;
    ptoken->str[0] = 0;
    bool foundDot = false;

    int i;
    char* s = pci->in_file.GetNextTokenStr();
    if (!s)
    {
        ptoken->type = ENDFILE;
        ptoken->str[0] = 0;
        return;
    }

    for (i = 0; i < num_symbolic_tokens; i++)
    {
        if (StartsWith(s, symbolic_tokens[i].str))
            break;
    }

    if (i < num_symbolic_tokens)
    {
        if (symbolic_tokens[i].type == LEFT_BRACE)
        {
            pci->in_file.Advance(strlen(symbolic_tokens[i].str));
            if (!pci->in_file.SkipUpto(symbolic_tokens[i + 1].str)) return;
            return GetNextToken(pci, ptoken);
        }
        ptoken->type = symbolic_tokens[i].type;
        Copy(ptoken->str, symbolic_tokens[i].str);
    }
    else if (IsDoubleOrInteger(s[0], &foundDot))          // checking for digits or a dot.
    {
        int j = 1;
        while (IsDoubleOrInteger(s[j], &foundDot)) j++;      // increase J while the character is digit or a dot.

        if (foundDot) ptoken->type = REAL;                   // if there is a dot found then this is a real number.
        else ptoken->type = INT;                             // else then this is an integer.
        //ptoken->type = REAL;
        Copy(ptoken->str, s, j);                             // copy token into str variable with len of J.
    }
    else if (IsLetterOrUnderscore(s[0]))
    {
        int j = 1;
        while (IsLetterOrUnderscore(s[j])) j++;

        ptoken->type = ID;
        Copy(ptoken->str, s, j);

        for (i = 0; i < num_reserved_words; i++)
        {
            if (Equals(ptoken->str, reserved_words[i].str))
            {
                ptoken->type = reserved_words[i].type;
                break;
            }
        }
    }

    int len = strlen(ptoken->str);
    if (len > 0) pci->in_file.Advance(len);
}

////////////////////////////////////////////////////////////////////////////////////
// Parser //////////////////////////////////////////////////////////////////////////

// program -> stmtseq
// stmtseq -> stmt { ; stmt }
// stmt -> ifstmt | repeatstmt | assignstmt | readstmt | writestmt | initializestmt
// ifstmt -> if exp then stmtseq [ else stmtseq ] end
// repeatstmt -> repeat stmtseq until expr
// assignstmt -> identifier := expr
// initializestmt -> int identifier | bool identifier | real identifier
// readstmt -> read identifier
// writestmt -> write expr
// expr -> mathexpr [ (<|=) mathexpr ]
// mathexpr -> SpecialAbsExpr { (+|-) SpecialAbsExpr }    left associative
// SpecialAbsExpr ->  term { (&) term } left associative
// term -> factor { (*|/) factor }    left associative
// factor -> newexpr { ^ newexpr }    right associative
// newexpr -> ( mathexpr ) | number | identifier | boolean

enum NodeKind {
    IF_NODE, REPEAT_NODE, ASSIGN_NODE, READ_NODE, WRITE_NODE,
    OPER_NODE, INT_NODE, REAL_NODE, ID_NODE, INIT_NODE, BOOL_NODE // defined INT_NODE, REAL_NODE, INIT_NODE and BOOL_NODE.
};

// Used for debugging only /////////////////////////////////////////////////////////
const char* NodeKindStr[] =
{
    "If", "Repeat", "Assign", "Read", "Write",
    "Oper", "Int", "Real", "ID", "Init", "Bool",        // defined Int, Real, Init and Bool Strings.
};

enum ExprDataType { VOID, INTEGER, BOOLEAN, REALNUM }; // defined REALNUM for Real Numbers.

// Used for debugging only /////////////////////////////////////////////////////////
const char* ExprDataTypeStr[] =
{
    "Void", "Integer", "Boolean", "Real"               // defined Real String for Real Numbers.
};

#define MAX_CHILDREN 3

struct TreeNode
{
    TreeNode* child[MAX_CHILDREN];
    TreeNode* sibling; // used for sibling statements only

    NodeKind node_kind;

    union { TokenType oper; char* value; char* id; bool boolean; };      // defined for expression/real/int/bool/identifier only
    ExprDataType expr_data_type;                                        // defined for expression/real/int/bool/identifier only

    int line_num;

    TreeNode() { int i; for (i = 0; i < MAX_CHILDREN; i++) child[i] = 0; sibling = 0; value = 0; expr_data_type = VOID; }
};

struct ParseInfo
{
    Token next_token;
};

void Match(CompilerInfo* pci, ParseInfo* ppi, TokenType expected_token_type)
{
    pci->debug_file.Out("Start Match");

    if (ppi->next_token.type != expected_token_type) { printf("ERROR expected %s put found %s\n", TokenTypeStr[expected_token_type], TokenTypeStr[ppi->next_token.type]); }
    GetNextToken(pci, &ppi->next_token);

    fprintf(pci->debug_file.file, "[%d] %s (%s)\n", pci->in_file.cur_line_num, ppi->next_token.str, TokenTypeStr[ppi->next_token.type]); fflush(pci->debug_file.file);
}

TreeNode* Expr(CompilerInfo*, ParseInfo*);

// newexpr -> ( mathexpr ) | number | identifier | boolean
TreeNode* NewExpr(CompilerInfo* pci, ParseInfo* ppi)
{
    pci->debug_file.Out("Start NewExpr");

    // Compare the next token with the First() of possible statements
    if (ppi->next_token.type == INT)
    {
        TreeNode* tree = new TreeNode;                              // create new tree node.
        tree->node_kind = INT_NODE;                                 // set node kind as integer node.
        char* num_str = ppi->next_token.str;                        // set num_str variable with the string number of the token.
        tree->value = 0; AllocateAndCopy(&tree->value, num_str);    // copy the num_str into tree.value .
        tree->line_num = pci->in_file.cur_line_num;                 // set the tree line number.
        Match(pci, ppi, ppi->next_token.type);                      // check for the current token type and get the next token.

        pci->debug_file.Out("End NewExpr");                      // print in debug file "End New Expr".
        return tree;                                                // return tree defined before.
    }

    if (ppi->next_token.type == REAL)
    {
        TreeNode* tree = new TreeNode;                              // create new tree node.
        tree->node_kind = REAL_NODE;                                // set node kind as real node.
        char* num_str = ppi->next_token.str;                        // set num_str variable with the string number of the token.
        tree->value = 0; AllocateAndCopy(&tree->value, num_str);    // copy the num_str into tree.value .
        tree->line_num = pci->in_file.cur_line_num;                 // set the tree line number.
        Match(pci, ppi, ppi->next_token.type);                      // check for the current token type and get the next token.

        pci->debug_file.Out("End NewExpr");                      // print in debug file "End New Expr".
        return tree;                                                // return tree defined before.
    }

    if (ppi->next_token.type == TRUE)
    {
        TreeNode* tree = new TreeNode;                              // create new tree node.
        tree->node_kind = BOOL_NODE;                                // set node kind as boolean node.
        tree->boolean = true;                                       // set tree boolean variable with true.
        tree->line_num = pci->in_file.cur_line_num;                 // set the tree line number.
        Match(pci, ppi, ppi->next_token.type);                      // check for the current token type and get the next token.

        pci->debug_file.Out("End NewExpr");                      // print in debug file "End New Expr".
        return tree;                                                // return tree defined before.
    }

    if(ppi->next_token.type == FALSE)
    {
        TreeNode* tree = new TreeNode;                              // create new tree node.
        tree->node_kind = BOOL_NODE;                                // set node kind as boolean node.
        tree->boolean = false;                                      // set tree boolean variable with false.
        tree->line_num = pci->in_file.cur_line_num;                 // set the tree line number.
        Match(pci, ppi, ppi->next_token.type);                      // check for the current token type and get the next token.

        pci->debug_file.Out("End NewExpr");                      // print in debug file "End New Expr".
        return tree;                                                // return tree defined before.
    }

    if (ppi->next_token.type == ID)
    {
        TreeNode* tree = new TreeNode;
        tree->node_kind = ID_NODE;
        AllocateAndCopy(&tree->id, ppi->next_token.str);
        tree->line_num = pci->in_file.cur_line_num;
        Match(pci, ppi, ppi->next_token.type);

        pci->debug_file.Out("End NewExpr");
        return tree;
    }

    if (ppi->next_token.type == LEFT_PAREN)
    {
        Match(pci, ppi, LEFT_PAREN);
        TreeNode* tree = Expr(pci, ppi);
        Match(pci, ppi, RIGHT_PAREN);

        pci->debug_file.Out("End NewExpr");
        return tree;
    }

    throw 0;
    return 0;
}

// factor -> newexpr { ^ newexpr }    right associative
TreeNode* Factor(CompilerInfo* pci, ParseInfo* ppi)
{
    pci->debug_file.Out("Start Factor");

    TreeNode* tree = NewExpr(pci, ppi);

    if (ppi->next_token.type == POWER)
    {
        TreeNode* new_tree = new TreeNode;
        new_tree->node_kind = OPER_NODE;
        new_tree->oper = ppi->next_token.type;
        new_tree->line_num = pci->in_file.cur_line_num;

        new_tree->child[0] = tree;
        Match(pci, ppi, ppi->next_token.type);
        new_tree->child[1] = Factor(pci, ppi);

        pci->debug_file.Out("End Factor");
        return new_tree;
    }
    pci->debug_file.Out("End Factor");
    return tree;
}

// term -> factor { (*|/) factor }    left associative
TreeNode* Term(CompilerInfo* pci, ParseInfo* ppi)
{
    pci->debug_file.Out("Start Term");

    TreeNode* tree = Factor(pci, ppi);

    while (ppi->next_token.type == TIMES || ppi->next_token.type == DIVIDE)
    {
        TreeNode* new_tree = new TreeNode;
        new_tree->node_kind = OPER_NODE;
        new_tree->oper = ppi->next_token.type;
        new_tree->line_num = pci->in_file.cur_line_num;

        new_tree->child[0] = tree;
        Match(pci, ppi, ppi->next_token.type);
        new_tree->child[1] = Factor(pci, ppi);

        tree = new_tree;
    }
    pci->debug_file.Out("End Term");
    return tree;
}

// SpecialAbsExpr -> Term { (&) Term } left associative
TreeNode* SpecialAbsExpr(CompilerInfo* pci, ParseInfo* ppi)
{
    pci->debug_file.Out("Start SpecialAbsExpr");        //write into debug file "Start SpecialAbsExpr".

    TreeNode* tree=Term(pci, ppi);                         //create new tree node for the Term Tree.

    while(ppi->next_token.type==ABSDIFF)                   //loop on while tokens are ABSDIFF operator.
    {
        TreeNode* new_tree=new TreeNode;                   //create new node tree for Special Absolute Expression
        new_tree->node_kind=OPER_NODE;                     //set the node type to be an operator node.
        new_tree->oper=ppi->next_token.type;               //set node operator to be the next token type string.
        new_tree->line_num=pci->in_file.cur_line_num;      //set the current token line number.

        new_tree->child[0]=tree;                           //set first child for the Special Absolute Expression tree node (tree) to be the tree returned from (Term function).
        Match(pci, ppi, ppi->next_token.type);             //call match function that checks the token validation and calls GetNextToken() function to get the next token.
        new_tree->child[1]=Term(pci, ppi);                 //set second child for the Special Absolute Expression tree node (tree) to be the operand.

        tree=new_tree;                                     //set the Special Absolute Expression tree node (tree) to be the new_tree node.
    }
    pci->debug_file.Out("End SpecialAbsExpr");          //write into debug file "End SpecialAbsExpr".
    return tree;                                           //return the tree created for the SpecialAbsExpr(tree).
}

// mathexpr -> SpecialAbsExpr { (+|-) SpecialAbsExpr }    left associative
TreeNode* MathExpr(CompilerInfo* pci, ParseInfo* ppi)
{
    pci->debug_file.Out("Start MathExpr");

    TreeNode* tree = SpecialAbsExpr(pci, ppi);

    while (ppi->next_token.type == PLUS || ppi->next_token.type == MINUS)
    {
        TreeNode* new_tree = new TreeNode;
        new_tree->node_kind = OPER_NODE;
        new_tree->oper = ppi->next_token.type;
        new_tree->line_num = pci->in_file.cur_line_num;

        new_tree->child[0] = tree;
        Match(pci, ppi, ppi->next_token.type);
        new_tree->child[1] = SpecialAbsExpr(pci, ppi);

        tree = new_tree;
    }
    pci->debug_file.Out("End MathExpr");
    return tree;
}

// expr -> mathexpr [ (<|=) mathexpr ]
TreeNode* Expr(CompilerInfo* pci, ParseInfo* ppi)
{
    pci->debug_file.Out("Start Expr");

    TreeNode* tree = MathExpr(pci, ppi);

    if (ppi->next_token.type == EQUAL || ppi->next_token.type == LESS_THAN)
    {
        TreeNode* new_tree = new TreeNode;
        new_tree->node_kind = OPER_NODE;
        new_tree->oper = ppi->next_token.type;
        new_tree->line_num = pci->in_file.cur_line_num;

        new_tree->child[0] = tree;
        Match(pci, ppi, ppi->next_token.type);
        new_tree->child[1] = MathExpr(pci, ppi);

        pci->debug_file.Out("End Expr");
        return new_tree;
    }
    pci->debug_file.Out("End Expr");
    return tree;
}

// writestmt -> write expr
TreeNode* WriteStmt(CompilerInfo* pci, ParseInfo* ppi)
{
    pci->debug_file.Out("Start WriteStmt");

    TreeNode* tree = new TreeNode;
    tree->node_kind = WRITE_NODE;
    tree->line_num = pci->in_file.cur_line_num;

    Match(pci, ppi, WRITE);
    tree->child[0] = Expr(pci, ppi);

    pci->debug_file.Out("End WriteStmt");
    return tree;
}

// readstmt -> read identifier
TreeNode* ReadStmt(CompilerInfo* pci, ParseInfo* ppi)
{
    pci->debug_file.Out("Start ReadStmt");

    TreeNode* tree = new TreeNode;
    tree->node_kind = READ_NODE;
    tree->line_num = pci->in_file.cur_line_num;

    Match(pci, ppi, READ);
    if (ppi->next_token.type == ID) AllocateAndCopy(&tree->id, ppi->next_token.str);
    Match(pci, ppi, ID);

    pci->debug_file.Out("End ReadStmt");
    return tree;
}

// initializestmt -> int identifier | bool identifier | real identifier
TreeNode* InitializeStmt(CompilerInfo* pci, ParseInfo* ppi) {
    pci->debug_file.Out("Start InitializeStmt");             // print in debug file "Start InitializeStmt"
    TreeNode* tree = new TreeNode;                              // create new Tree node.
    tree->node_kind = INIT_NODE;                                // set node kind as a INIT_NODE.
    tree->line_num = pci->in_file.cur_line_num;                 // set the line number.
    if (ppi->next_token.type == INT)                            // if current token is an integer.
    {
        Match(pci, ppi, INT);                   // then match current token type with Int and get the next token.
        tree->expr_data_type = INTEGER;                         // set expression data type with INTEGER.
    }
    else if (ppi->next_token.type == BOOL)                      // if current token is a boolean.
    {
        Match(pci, ppi, BOOL);                  // then match current token type with Bool and get the next token.
        tree->expr_data_type = BOOLEAN;                         // set expression data type with BOOLEAN.
    }
    else if (ppi->next_token.type == REAL)                      // if current token is a real.
    {
        tree->expr_data_type = REALNUM;                         // then match current token type with Real and get the next token.
        Match(pci, ppi, REAL);                  // set expression data type with REAL.
    }
    if (ppi->next_token.type == ID) AllocateAndCopy(&tree->id, ppi->next_token.str); Match(pci, ppi, ID);
                                                                // if current token type is an ID then copy the ID name into tree.id.
                                                                // then match current token with ID, and get the next token.

    pci->debug_file.Out("End InitializeStmt");               // print in debug file "End InitializeStmt"
    return tree;                                                // return tree defined before.
}

// assignstmt -> identifier := expr
TreeNode* AssignStmt(CompilerInfo* pci, ParseInfo* ppi)
{
    pci->debug_file.Out("Start AssignStmt");

    TreeNode* tree = new TreeNode;
    tree->node_kind = ASSIGN_NODE;
    tree->line_num = pci->in_file.cur_line_num;

    if (ppi->next_token.type == ID) AllocateAndCopy(&tree->id, ppi->next_token.str); Match(pci, ppi, ID);

    Match(pci, ppi, ASSIGN);
    tree->child[0] = Expr(pci, ppi);

    pci->debug_file.Out("End AssignStmt");
    return tree;
}

TreeNode* StmtSeq(CompilerInfo*, ParseInfo*);

// repeatstmt -> repeat stmtseq until expr
TreeNode* RepeatStmt(CompilerInfo* pci, ParseInfo* ppi)
{
    pci->debug_file.Out("Start RepeatStmt");

    TreeNode* tree = new TreeNode;
    tree->node_kind = REPEAT_NODE;
    tree->line_num = pci->in_file.cur_line_num;

    Match(pci, ppi, REPEAT); tree->child[0] = StmtSeq(pci, ppi);
    Match(pci, ppi, UNTIL); tree->child[1] = Expr(pci, ppi);

    pci->debug_file.Out("End RepeatStmt");
    return tree;
}

// ifstmt -> if exp then stmtseq [ else stmtseq ] end
TreeNode* IfStmt(CompilerInfo* pci, ParseInfo* ppi)
{
    pci->debug_file.Out("Start IfStmt");

    TreeNode* tree = new TreeNode;
    tree->node_kind = IF_NODE;
    tree->line_num = pci->in_file.cur_line_num;

    Match(pci, ppi, IF); tree->child[0] = Expr(pci, ppi);
    Match(pci, ppi, THEN); tree->child[1] = StmtSeq(pci, ppi);
    if (ppi->next_token.type == ELSE) { Match(pci, ppi, ELSE); tree->child[2] = StmtSeq(pci, ppi); }
    Match(pci, ppi, END);

    pci->debug_file.Out("End IfStmt");
    return tree;
}

// stmt -> ifstmt | repeatstmt | assignstmt | readstmt | writestmt
TreeNode* Stmt(CompilerInfo* pci, ParseInfo* ppi)
{
    pci->debug_file.Out("Start Stmt");

    // Compare the next token with the First() of possible statements
    TreeNode* tree = 0;
    if (ppi->next_token.type == IF) tree = IfStmt(pci, ppi);
    else if (ppi->next_token.type == REPEAT) tree = RepeatStmt(pci, ppi);
    else if (ppi->next_token.type == ID) tree = AssignStmt(pci, ppi);
    else if (ppi->next_token.type == INT || ppi->next_token.type == BOOL || ppi->next_token.type == REAL) tree = InitializeStmt(pci, ppi);
                                                                                // check for int, bool, and real then go to InitializeStmt function to initialize the variable.
    else if (ppi->next_token.type == READ) tree = ReadStmt(pci, ppi);
    else if (ppi->next_token.type == WRITE) tree = WriteStmt(pci, ppi);
    else throw 0;

    pci->debug_file.Out("End Stmt");
    return tree;
}

// stmtseq -> stmt { ; stmt }
TreeNode* StmtSeq(CompilerInfo* pci, ParseInfo* ppi)
{
    pci->debug_file.Out("Start StmtSeq");

    TreeNode* first_tree = Stmt(pci, ppi);
    TreeNode* last_tree = first_tree;

    // If we did not reach one of the Follow() of StmtSeq(), we are not done yet
    while (ppi->next_token.type != ENDFILE && ppi->next_token.type != END &&
        ppi->next_token.type != ELSE && ppi->next_token.type != UNTIL)
    {
        Match(pci, ppi, SEMI_COLON);
        TreeNode* next_tree = Stmt(pci, ppi);
        last_tree->sibling = next_tree;
        last_tree = next_tree;
    }

    pci->debug_file.Out("End StmtSeq");
    return first_tree;
}

// program -> stmtseq
TreeNode* Parse(CompilerInfo* pci)
{
    ParseInfo parse_info;
    GetNextToken(pci, &parse_info.next_token);

    TreeNode* syntax_tree = StmtSeq(pci, &parse_info);

    if (parse_info.next_token.type != ENDFILE)
        pci->debug_file.Out("Error code ends before file ends");

    return syntax_tree;
}

void PrintTree(TreeNode* node, int sh = 0)
{
    int i, NSH = 3;
    for (i = 0; i < sh; i++) printf(" ");

    printf("[%s]", NodeKindStr[node->node_kind]);

    if (node->node_kind == OPER_NODE) printf("[%s]", TokenTypeStr[node->oper]);
    else if (node->node_kind == INT_NODE || node->node_kind == REAL_NODE) printf("[%s]", node->value);
    else if (node->node_kind == BOOL_NODE) printf("%d", node->value);
    else if (node->node_kind == ID_NODE || node->node_kind == READ_NODE || node->node_kind == ASSIGN_NODE || node->node_kind == INIT_NODE) printf("[%s]", node->id);
    if (node->expr_data_type != VOID || node->node_kind == OPER_NODE) printf("[%s]", ExprDataTypeStr[node->expr_data_type]);

    printf("\n");

    for (i = 0; i < MAX_CHILDREN; i++) if (node->child[i]) PrintTree(node->child[i], sh + NSH);
    if (node->sibling) PrintTree(node->sibling, sh);
}

void DestroyTree(TreeNode* node)
{
    int i;

    if (node->node_kind == ID_NODE || node->node_kind == READ_NODE || node->node_kind == ASSIGN_NODE || node->node_kind == INIT_NODE)
        if (node->id) delete[] node->id;

    for (i = 0; i < MAX_CHILDREN; i++) if (node->child[i]) DestroyTree(node->child[i]);
    if (node->sibling) DestroyTree(node->sibling);

    delete node;
}

////////////////////////////////////////////////////////////////////////////////////
// Analyzer ////////////////////////////////////////////////////////////////////////

const int SYMBOL_HASH_SIZE = 10007;

struct LineLocation
{
    int line_num;
    LineLocation* next;
};

struct VariableInfo
{
    char* name;
    int memloc;
    ExprDataType expr_data_type; // the expression data type contains the data type of the variable (int, bool, real).
    LineLocation* head_line; // the head of linked list of source line locations
    LineLocation* tail_line; // the tail of linked list of source line locations
    VariableInfo* next_var; // the next variable in the linked list in the same hash bucket of the symbol table
};

struct SymbolTable
{
    int num_vars;
    VariableInfo* var_info[SYMBOL_HASH_SIZE];

    SymbolTable() { num_vars = 0; int i; for (i = 0; i < SYMBOL_HASH_SIZE; i++) var_info[i] = 0; }

    int Hash(const char* name)
    {
        int i, len = strlen(name);
        int hash_val = 11;
        for (i = 0; i < len; i++) hash_val = (hash_val * 17 + (int)name[i]) % SYMBOL_HASH_SIZE;
        return hash_val;
    }

    VariableInfo* Find(const char* name)
    {
        int h = Hash(name);
        VariableInfo* cur = var_info[h];
        while (cur)
        {
            if (Equals(name, cur->name)) return cur;
            cur = cur->next_var;
        }
        return 0;
    }

    void Insert(const char* name, int line_num, ExprDataType expr_data_type)
    {
        LineLocation* lineloc = new LineLocation;
        lineloc->line_num = line_num;
        lineloc->next = 0;

        int h = Hash(name);
        VariableInfo* prev = 0;
        VariableInfo* cur = var_info[h];

        while (cur)
        {
            if (Equals(name, cur->name))
            {
                // just add this line location to the list of line locations of the existing var
                cur->tail_line->next = lineloc;
                cur->tail_line = lineloc;
                return;
            }
            prev = cur;
            cur = cur->next_var;
        }

        VariableInfo* vi = new VariableInfo;
        vi->head_line = vi->tail_line = lineloc;
        vi->next_var = 0;
        vi->memloc = num_vars++;
        vi->expr_data_type = expr_data_type;
        AllocateAndCopy(&vi->name, name);

        if (!prev) var_info[h] = vi;
        else prev->next_var = vi;
    }

    void Print()
    {
        int i;
        for (i = 0; i < SYMBOL_HASH_SIZE; i++)
        {
            VariableInfo* curv = var_info[i];
            while (curv)
            {
                printf("[Var=%s][Mem=%d]", curv->name, curv->memloc);
                LineLocation* curl = curv->head_line;
                while (curl)
                {
                    printf("[Line=%d]", curl->line_num);
                    curl = curl->next;
                }
                printf("\n");
                curv = curv->next_var;
            }
        }
    }

    void Destroy()
    {
        int i;
        for (i = 0; i < SYMBOL_HASH_SIZE; i++)
        {
            VariableInfo* curv = var_info[i];
            while (curv)
            {
                LineLocation* curl = curv->head_line;
                while (curl)
                {
                    LineLocation* pl = curl;
                    curl = curl->next;
                    delete pl;
                }
                VariableInfo* p = curv;
                curv = curv->next_var;
                delete p;
            }
            var_info[i] = 0;
        }
    }
};

bool isDeclarationPhase = true;

void Analyze(TreeNode* node, SymbolTable* symbol_table)
{
    int i;

    if(node->node_kind == INIT_NODE && !isDeclarationPhase) // checking for any variable define not in the beginning of the program.
        { printf("ERROR Declaration has stopped. you must declare your variables (%s) at the beginning of the program.\n", node->id);  throw 0; }//print ERROR then throw.

    if (node->node_kind == INIT_NODE)       // checking for initialization nodes.
    {
        if(symbol_table->Find(node->id) != nullptr) { printf("ERROR the variable ( %s ) declared before.\n", node->id); throw 0; }
                                                    // checking if the variable defined before, if so print ERROR then throw.
        symbol_table->Insert(node->id, node->line_num, node->expr_data_type);  // insert new variable in the symbol table.
    }
    if (node->node_kind == ASSIGN_NODE)     // checking for assignment nodes.
    {
        VariableInfo *var_info = symbol_table->Find(node->id);      // checking for variable initialized.
        if (var_info == nullptr)                                    // if variable not initialized.
        { printf("ERROR VARIABLES ( %s ) must be declared before use!\n", node->id); throw 0;}  // print Error variables must be declared before use!
    }

    for (i = 0; i < MAX_CHILDREN; i++) if (node->child[i]) Analyze(node->child[i], symbol_table);

    if (node->node_kind == OPER_NODE) {
        if (node->oper == EQUAL || node->oper == LESS_THAN) node->expr_data_type = BOOLEAN;
        if (node->child[0]->expr_data_type == INTEGER && node->child[1]->expr_data_type == INTEGER)         // if first child and second child of type integer.
            node->expr_data_type = INTEGER;                                                                 // then parent will be integer.
        else if (node->child[0]->expr_data_type == REALNUM && node->child[1]->expr_data_type == REALNUM)    // if first child and second child of type integer.
            node->expr_data_type = REALNUM;                                                                 // then parent will be integer.
        isDeclarationPhase = false;                                                                         // end declaration Phase.
    }
    else if ( node->node_kind == ID_NODE ) { node->expr_data_type = symbol_table->Find(node->id)->expr_data_type; isDeclarationPhase = false; } // end declaration phase
    else if( node->node_kind == INT_NODE ) { node->expr_data_type = INTEGER; }      // if node kind is int then expression data type = INTEGER
    else if( node->node_kind == REAL_NODE ) { node->expr_data_type = REALNUM; }     // if node kind is real then expression data type = REALNUM
    else if( node->node_kind == BOOL_NODE ) { node->expr_data_type = BOOLEAN; }     // if node kind is bool then expression data type = BOOLEAN

    if (node->node_kind == OPER_NODE)
    {
        if ((node->child[0]->expr_data_type != node->child[1]->expr_data_type) || (node->oper != EQUAL && node->oper != LESS_THAN &&
            (node->child[0]->expr_data_type == BOOLEAN || node->child[1]->expr_data_type == BOOLEAN)))
            // if (first child expression data type not equal second child expression data type)
            // or (node operation not equal and not lessThan and first child or second child expression data type = boolean.
            { printf("ERROR Operator applied to variables ( %s ) ( %s ) of the same type only\n", node->child[0]->id, node->child[1]->id); throw 0; }
            // then print Error operation must be applied to same data type.
        isDeclarationPhase = false; // end declaration phase.
    }

    if (node->node_kind == ASSIGN_NODE)     // checking for assignment nodes.
    {
        VariableInfo* var_info = symbol_table->Find(node->id);
        if(var_info && var_info->expr_data_type != node->child[0]->expr_data_type) // if var exists and var expression data type not equal first child expression data type.
            { printf("ERROR the variable ( %s ) must assigned to value of the same type.\n", var_info->name);} // then print ERROR and throw.
        symbol_table->Insert(node->id, node->line_num, node->expr_data_type);       // insert variable into symbol table.
        isDeclarationPhase = false;     //end declaration phase
    }
    if ((node->node_kind == ID_NODE || node->node_kind == READ_NODE || node->node_kind == INIT_NODE) && node->expr_data_type == VOID) // if use var without declaring it
        { printf("ERROR Variable ( %s ) must be declared before use\n", node->id); throw 0;}                                          // then print ERROR and throw.

    if (node->sibling) Analyze(node->sibling, symbol_table);
}

////////////////////////////////////////////////////////////////////////////////////
// Code Generator //////////////////////////////////////////////////////////////////

double Power(double a, double b)
{
    if (a == 0) return 0;
    if (b == 0) return 1;
    if (b >= 1) return a * Power(a, b - 1);
    return 0;
}

double abs_difference_double(double a, double b) // created absolute difference function.
{
    if (a > b) return a - b;                // checking if a is greater than b then return a - b.
    else if (a > b) return b - a;           // checking if b is greater than a then return b - a.
    else return a - b;                      // else return a - b.
}

double Evaluate(TreeNode* node, SymbolTable* symbol_table, double* variables)
{
    if (node->node_kind == INT_NODE || node->node_kind == REAL_NODE) return atof(node->value); // return atof(node->value) which convert string to double
    if (node->node_kind == BOOL_NODE) return node->boolean; // return atof(node->value) which convert string to double
    if (node->node_kind == ID_NODE) { return variables[symbol_table->Find(node->id)->memloc]; }

    double a = Evaluate(node->child[0], symbol_table, variables);
    double b = Evaluate(node->child[1], symbol_table, variables);

    if (node->oper == EQUAL) return a == b;
    if (node->oper == LESS_THAN) return a < b;
    if (node->oper == PLUS) return a + b;
    if (node->oper == MINUS) return a - b;
    if (node->oper == ABSDIFF) return abs_difference_double(a, b); // return absolute difference value.
    if (node->oper == TIMES) return a * b;
    if (node->oper == DIVIDE) return a / b;
    if (node->oper == POWER) return Power(a, b);
    throw 0;
    return 0;
}

void RunProgram(TreeNode* node, SymbolTable* symbol_table, double* variables)
{
    if (node->node_kind == IF_NODE)
    {
        int cond = Evaluate(node->child[0], symbol_table, variables);
        if (cond) RunProgram(node->child[1], symbol_table, variables);
        else if (node->child[2]) RunProgram(node->child[2], symbol_table, variables);
    }
    if (node->node_kind == INIT_NODE && node->child[0]) // if node kind is INIT_NODE.
    {
        RunProgram(node->child[0], symbol_table, variables);
    }
    if (node->node_kind == ASSIGN_NODE)
    {
        double v = Evaluate(node->child[0], symbol_table, variables);
        variables[symbol_table->Find(node->id)->memloc] = v;
    }
    if (node->node_kind == READ_NODE)
    {
        printf("Enter %s: ", node->id);
        scanf("%lf", &variables[symbol_table->Find(node->id)->memloc]);
    }
    if (node->node_kind == WRITE_NODE)
    {
        double v = Evaluate(node->child[0], symbol_table, variables);
        if(v == (int)v) printf("Val: %d\n", (int)v);
        else printf("Val: %lf\n", v);
    }
    if (node->node_kind == REPEAT_NODE)
    {
        do
        {
            RunProgram(node->child[0], symbol_table, variables);
        } while (!Evaluate(node->child[1], symbol_table, variables));
    }
    if (node->sibling) RunProgram(node->sibling, symbol_table, variables);
}

void RunProgram(TreeNode* syntax_tree, SymbolTable* symbol_table)
{
    int i;
    double* variables = new double[symbol_table->num_vars];
    for (i = 0; i < symbol_table->num_vars; i++) variables[i] = 0;
    RunProgram(syntax_tree, symbol_table, variables);
    delete[] variables;
}

////////////////////////////////////////////////////////////////////////////////////
// Scanner and Compiler ////////////////////////////////////////////////////////////

void StartCompiler(CompilerInfo* pci)
{
    TreeNode* syntax_tree = Parse(pci);

    SymbolTable symbol_table;
    Analyze(syntax_tree, &symbol_table);

    printf("Symbol Table:\n");
    symbol_table.Print();
    printf("---------------------------------\n"); fflush(NULL);

    printf("Syntax Tree:\n");
    PrintTree(syntax_tree);
    printf("---------------------------------\n"); fflush(NULL);

    printf("Run Program:\n");
    RunProgram(syntax_tree, &symbol_table);
    printf("---------------------------------\n"); fflush(NULL);

    symbol_table.Destroy();
    DestroyTree(syntax_tree);
}

////////////////////////////////////////////////////////////////////////////////////
// Scanner only ////////////////////////////////////////////////////////////////////

void StartScanner(CompilerInfo* pci)
{
    Token token;

    while (true)
    {
        GetNextToken(pci, &token);
        printf("[%d] %s (%s)\n", pci->in_file.cur_line_num, token.str, TokenTypeStr[token.type]); fflush(NULL);
        if (token.type == ENDFILE || token.type == ERROR) break;
    }
}

////////////////////////////////////////////////////////////////////////////////////

int main()
{
    printf("Start main()\n"); fflush(NULL);

    CompilerInfo compiler_info("input.txt", "output.txt", "debug.txt");

    StartCompiler(&compiler_info);

    printf("End main()\n"); fflush(NULL);
    return 0;
}

////////////////////////////////////////////////////////////////////////////////////
