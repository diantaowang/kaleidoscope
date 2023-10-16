#include "inc/kaleidoscopeJIT.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/Analysis/BasicAliasAnalysis.h"
#include "llvm/Analysis/Passes.h"
#include "llvm/IR/DIBuilder.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/TargetParser/Host.h"
#include "llvm/Transforms/Scalar.h"
#include <cctype>
#include <cstdio>
#include <map>
#include <memory>
#include <string>
#include <vector>

using namespace llvm;
using namespace llvm::orc;

//===----------------------------------------------------------------------===//
// Lexer
//===----------------------------------------------------------------------===//

// The lexer returns tokens [0-255] if it is an unknown character, otherwise one
// of these for known things.
enum Token {
    tok_eof = -1,

    // commands
    tok_def = -2,
    tok_extern = -3,

    // primary
    tok_identifier = -4,
    tok_number = -5,

    // control
    tok_if = -6,
    tok_then = -7,
    tok_else = -8,
    tok_for = -9,
    tok_in = -10,

    // operators
    tok_binary = -11,
    tok_unary = -12,

    // variable
    tok_var = -13
};

std::string getTokName(int tok) {
    switch (tok) {
        case tok_eof:
            return "eof";
        case tok_def:
            return "def";
        case tok_extern:
            return "extern";
        case tok_identifier:
            return "identifier";
        case tok_number:
            return "number";
        case tok_if:
            return "if";
        case tok_then:
            return "then";
        case tok_else:
            return "else";
        case tok_for:
            return "for";
        case tok_in:
            return "in";
        case tok_binary:
            return "binary";
        case tok_unary:
            return "unary";
        case tok_var:
            return "var";
        default:
            return std::string(1, (char)tok);
    }
}

namespace {
class ExprAST;
}

struct DebugInfo {
    DICompileUnit *TheCU;
    DIType *DblTy;
    std::vector<DIScope*> LexicalBlocks;

    void emitLocation(ExprAST *AST);
    DIType *getDoubleTy();
} KSDbgInfo;

struct SourceLocation {
    int Line;
    int Col;
};

static SourceLocation CurLoc;
static SourceLocation LexLoc = {1, 0};

static int advance() {
    int LastChar = getchar();
    if (LastChar == '\n' || LastChar == '\t') {
        ++LexLoc.Line;
        LexLoc.Col = 0;
    } else {
        ++LexLoc.Col;
    }
    return LastChar;
}

static std::string IdentifierStr; // Filled in if tok_identifier
static double NumVal;              // Filled in if tok_number

/// gettok - Return the next token from standard input.
static int gettok() {
    // Why need static? Because lexer uses look-ahead.
    static char LastChar = ' ';

    // Skip any whitespace.
    while (isspace(LastChar))
        LastChar = advance();

    CurLoc = LexLoc;

    if (isalpha(LastChar)) { // identifier: [a-zA-Z][a-zA-Z0-9]*
        IdentifierStr = LastChar;
        while (isalnum(LastChar = advance()))
            IdentifierStr += LastChar;
        if (IdentifierStr == "def")
            return tok_def;
        if (IdentifierStr == "extern")
            return tok_extern;
        if (IdentifierStr == "if")
            return tok_if;
        if (IdentifierStr == "then")
            return tok_then;
        if (IdentifierStr == "else")
            return tok_else;
        if (IdentifierStr == "for")
            return tok_for;
        if (IdentifierStr == "in")
            return tok_in;
        if (IdentifierStr == "binary")
            return tok_binary;
        if (IdentifierStr == "unary")
            return tok_unary;
        if (IdentifierStr == "var")
            return tok_var;
        return tok_identifier;
    }

    if (isdigit(LastChar) || LastChar == '.') { // Number: [0-9.]+
        std::string NumStr;
        do {
            NumStr += LastChar;
            LastChar = advance();
        } while (isdigit(LastChar) || LastChar == '.');
        NumVal = strtod(NumStr.c_str(), nullptr);
        return tok_number;
    }

    if (LastChar == '#') {
        // Comment until end of line.
        do {
            LastChar = advance();
        } while (LastChar != EOF && LastChar != '\n' && LastChar != '\r');
        if (LastChar != EOF)
            return gettok();
    }

    // Check for end of file.  Don't eat the EOF.
    if (LastChar == EOF)
        return tok_eof;

    // Otherwise, just return the character as its ascii value.
    char ThisChar = LastChar;
    LastChar = advance();
    // Why we need return the remain symbol? Because the remain symbol is also a part of grammar, like '+', '(', etc.
    return ThisChar;
}

//===----------------------------------------------------------------------===//
// Abstract Syntax Tree (aka Parse Tree)
//===----------------------------------------------------------------------===//

namespace {

raw_ostream &indent(raw_ostream &os, int size) {
    return os << std::string(size, ' ');
}

/// ExprAST - Base class for all expression nodes.
class ExprAST {
    SourceLocation Loc;
public:
    ExprAST(SourceLocation Loc = CurLoc) : Loc(Loc) {}
    virtual ~ExprAST() = default;
    virtual Value *codegen() = 0;
    int getLine() const { return Loc.Line; }
    int getCol() const { return Loc.Col; }
    virtual raw_ostream &dump(raw_ostream &out, int ind) {
        return out << ':' << getLine() << ':' << getCol() << '\n';
    }
};

/// NumberExprAST - Expression class for numeric literals like "1.0".
class NumberExprAST : public ExprAST {
    double Val;
public:
    NumberExprAST(double Val) : Val(Val) {}
    Value *codegen() override;
    raw_ostream &dump(raw_ostream &out, int ind) override {
        return ExprAST::dump(out << Val, ind);
    }
};

/// VariableExprAST - Expression class for referencing a variable, like "a".
class VariableExprAST : public ExprAST {
    std::string Name;
public:
    VariableExprAST(SourceLocation Loc, std::string Name) : ExprAST(Loc), Name(std::move(Name)) {}
    Value *codegen() override;
    const std::string &getName() const { return Name; }
    raw_ostream &dump(raw_ostream &out, int ind) override {
        return ExprAST::dump(out << Name, ind);
    }
};

/// UnaryExprAST - Expression class for a unary operator.
class UnaryExprAST : public ExprAST {
    char Opcode;
    std::unique_ptr<ExprAST> Operand;
public:
    UnaryExprAST(char Op, std::unique_ptr<ExprAST> Operand) : Opcode(Op), Operand(std::move(Operand)) {}
    Value *codegen() override;
    raw_ostream &dump(raw_ostream &out, int ind) override {
        ExprAST::dump(out << "unary" << Opcode, ind);
        Operand->dump(out, ind + 1);
        return out;
    }
};

/// BinaryExprAST - Expression class for a binary operator.
class BinaryExprAST : public ExprAST {
    char Opcode;
    std::unique_ptr<ExprAST> LHS, RHS;
public:
    BinaryExprAST(SourceLocation Loc, char Op, std::unique_ptr<ExprAST> LHS, 
            std::unique_ptr<ExprAST> RHS) :
        ExprAST(Loc), Opcode(Op), LHS(std::move(LHS)), RHS(std::move(RHS)) {}
    Value *codegen() override;
    raw_ostream &dump(raw_ostream &out, int ind) override {
        ExprAST::dump(out << "binary" << Opcode, ind);
        LHS->dump(indent(out, ind) << "LHS:", ind + 1);
        RHS->dump(indent(out, ind) << "RHS:", ind + 1);
        return out;
    }
};

/// CallExprAST - Expression class for function calls.
class CallExprAST : public ExprAST {
    std::string Callee;
    std::vector<std::unique_ptr<ExprAST>> Args;
public:
    CallExprAST(SourceLocation Loc, std::string Callee, std::vector<std::unique_ptr<ExprAST>> Args) :
        ExprAST(Loc), Callee(std::move(Callee)), Args(std::move(Args)) {}
    Value *codegen() override;
    raw_ostream &dump(raw_ostream &out, int ind) override {
        ExprAST::dump(out << "call " << Callee, ind);
        for (const auto &Arg : Args)
            Arg->dump(indent(out, ind + 1), ind + 1);
        return out;
    }
};

/// IfExprAST - Expression class for if/then/else.
class IfExprAST : public ExprAST {
    std::unique_ptr<ExprAST> Cond, Then, Else;
public:
    IfExprAST(SourceLocation Loc, std::unique_ptr<ExprAST> Cond, 
            std::unique_ptr<ExprAST> Then, std::unique_ptr<ExprAST> Else) :
        ExprAST(Loc), Cond(std::move(Cond)), Then(std::move(Then)), Else(std::move(Else)) {}
    Value *codegen() override;
    raw_ostream &dump(raw_ostream &out, int ind) override {
        ExprAST::dump(out << "if", ind);
        Cond->dump(indent(out, ind) << "Cond:", ind + 1);
        Then->dump(indent(out, ind) << "Then:", ind + 1);
        Else->dump(indent(out, ind) << "Else:", ind + 1);
        return out;
    }
};

/// ForExprAST - Expression class for for/in.
class ForExprAST : public ExprAST {
    std::string VarName;
    std::unique_ptr<ExprAST> Start, End, Step, Body;
public:
    ForExprAST(const std::string &VarName, std::unique_ptr<ExprAST> Start, std::unique_ptr<ExprAST> End, 
            std::unique_ptr<ExprAST> Step, std::unique_ptr<ExprAST> Body) :
        VarName(VarName), Start(std::move(Start)), End(std::move(End)), 
        Step(std::move(Step)), Body(std::move(Body)) {}
    Value *codegen() override;
    raw_ostream &dump(raw_ostream &out, int ind) override {
        ExprAST::dump(out << "for", ind);
        Start->dump(indent(out, ind) << "Start:", ind + 1);
        End->dump(indent(out, ind) << "End:", ind + 1);
        Step->dump(indent(out, ind) << "Step:", ind + 1);
        Body->dump(indent(out, ind) << "Body:", ind + 1);
        return out;
    }
};

/// VarExprAST - Expression class for var/in
class VarExprAST : public ExprAST {
    std::vector<std::pair<std::string, std::unique_ptr<ExprAST>>> VarNames;
    std::unique_ptr<ExprAST> Body;
public:
    VarExprAST(std::vector<std::pair<std::string, std::unique_ptr<ExprAST>>> VarNames, 
            std::unique_ptr<ExprAST> Body) : 
        VarNames(std::move(VarNames)), Body(std::move(Body)) {}
    Value *codegen() override;
    raw_ostream &dump(raw_ostream &out, int ind) override {
        ExprAST::dump(out << "var", ind);
        for (const auto &VarName : VarNames)
            VarName.second->dump(indent(out, ind) << VarName.first << ':', ind + 1); // TODO
        Body->dump(indent(out, ind) << "Body:", ind + 1);
        return out;
    }
};

/// PrototypeAST - This class represents the "prototype" for a function,
/// which captures its name, and its argument names (thus implicitly the number
/// of arguments the function takes).
class FunctionAST;
class PrototypeAST {
friend FunctionAST;
    std::string Name;
    std::vector<std::string> Args;
    bool IsOperator;
    unsigned Precedence;
    int Line;
public:
    PrototypeAST(SourceLocation Loc, std::string Name, std::vector<std::string> Args, 
            bool IsOperator = false, unsigned Prec = 0) :
        Name(std::move(Name)), Args(std::move(Args)), IsOperator(IsOperator), 
        Precedence(Prec), Line(Loc.Line) {}
    
    Function *codegen();
    const std::string &getName() const { return Name; }

    bool isUnaryOp() const { return IsOperator && Args.size() == 1; }
    bool isBinaryOp() const { return IsOperator && Args.size() == 2; }

    char getOperatorName() const {
        assert(isUnaryOp() || isBinaryOp());
        return Name.back();
    }

    unsigned getBinaryPrecedence() const { return Precedence; }
    int getLine() const { return Line; }
};

/// FunctionAST - This class represents a function definition itself.
class FunctionAST {
    std::unique_ptr<PrototypeAST> Proto;
    std::unique_ptr<ExprAST> Body;
public:
    FunctionAST(std::unique_ptr<PrototypeAST> Proto, std::unique_ptr<ExprAST> Body) :
        Proto(std::move(Proto)), Body(std::move(Body)) {}

    Function *codegen(); 
    raw_ostream &dump(raw_ostream &out, int ind) {
        indent(out, ind);
        ++ind;
        indent(out, ind) << "Body:";
        return Body ? Body->dump(out, ind) : out << "null\n";
    }       
};
} // end anonymous namespace

//===----------------------------------------------------------------------===//
// Parser
//===----------------------------------------------------------------------===//

/// CurTok/getNextToken - Provide a simple token buffer.  CurTok is the current
/// token the parser is looking at.  getNextToken reads another token from the
/// lexer and updates CurTok with its results.
static int CurTok;
static int getNextToken() {
    CurTok = gettok();
    return CurTok;
};

/// BinopPrecedence - This holds the precedence for each binary operator that is
/// defined.
static std::map<char, int> BinopPrecedence;

static int GetTokPrecedence() {
    if (!isascii(CurTok))
        return -1;
    // Make sure it's a declared binop.
    auto TokPrecIter = BinopPrecedence.find(CurTok);
    if (TokPrecIter == BinopPrecedence.end())
        return -1;
    return TokPrecIter->second;
}

/// LogError* - These are little helper functions for error handling.
std::unique_ptr<ExprAST> LogError(const char *Str) {
    fprintf(stderr, "Error: %s\n", Str);
    return nullptr;
}

std::unique_ptr<PrototypeAST> LogErrorP(const char *Str) {
    fprintf(stderr, "Error: %s\n", Str);
    return nullptr;
}

static std::unique_ptr<ExprAST> ParseExpression();

/// numberexpr ::= number
static std::unique_ptr<ExprAST> ParseNumberExpr() {
    auto result = std::make_unique<NumberExprAST>(NumVal);
    getNextToken(); // consume the number
    return result;
}

/// parenexpr ::= '(' expression ')'
static std::unique_ptr<ExprAST> ParseParenExpr() {
    getNextToken(); // eat (.
    auto V = ParseExpression();
    // Why do we need to return a nullptr instead of reporting an error? Because we have reported the error when parse expression.
    if (!V)
        return nullptr;
    if (CurTok != ')')
        return LogError("expected ')'");
    getNextToken(); // eat ).
    return V;
}

/// identifierexpr
///   ::= identifier
///   ::= identifier '(' expression* ')'
static std::unique_ptr<ExprAST> ParseIdentifierExpr() {
    std::string IdName = IdentifierStr;
    auto LitLoc = CurLoc;

    getNextToken();  // eat identifier.
    if (CurTok != '(') // Simple variable ref.
        return std::make_unique<VariableExprAST>(LitLoc, IdName);

    // Call.
    getNextToken(); // eat (
    std::vector<std::unique_ptr<ExprAST>> Args;
    if (CurTok != ')') {
        while (true) {
            if (auto arg = ParseExpression())
                Args.push_back(std::move(arg));
            else
                return nullptr; // Why do we need to return a nullptr instead of reporting an error? Because we have reported the error when parse arg.
            if (CurTok == ')')
                break;
            if (CurTok != ',')
                return LogError("Expected ')' or ',' in argument list");
            getNextToken();
        }
    }
    // Eat the ')'.
    getNextToken();
    return std::make_unique<CallExprAST>(LitLoc, IdName, std::move(Args));
}

/// ifexpr ::= 'if' expression 'then' expression 'else' expression
static std::unique_ptr<ExprAST> ParseIfExpr() {
    auto IfLoc = CurLoc;
    
    getNextToken(); // eat the if.
    
    auto Cond = ParseExpression();
    if (!Cond)
        return nullptr;
    
    if (CurTok != tok_then)
        LogError("expected then");
    getNextToken(); // eat the then.

    auto Then = ParseExpression();
    if (!Then)
        return nullptr;
    
    if (CurTok != tok_else)
        LogError("expected else");
    getNextToken(); // eat the else.

    auto Else = ParseExpression();
    if (!Else)
        return nullptr;

    return std::make_unique<IfExprAST>(IfLoc, std::move(Cond), std::move(Then), std::move(Else));
}

/// forexpr ::= 'for' identifier '=' expr ',' expr (',' expr)? 'in' expression
static std::unique_ptr<ExprAST> ParseForExpr() {
    getNextToken(); // eat the for.
    
    if (CurTok != tok_identifier)
        return LogError("expected indentifier after for");
    std::string IdName = IdentifierStr;
    getNextToken();
    
    if (CurTok != '=')
        return LogError("expected '=' after for");
    getNextToken();
    
    auto Start = ParseExpression();
    if (!Start)
        return nullptr;
    
    if (CurTok != ',')
        return LogError("expected ',' after for");
    getNextToken(); 

    auto End = ParseExpression();
    if (!End)
        return nullptr;

    std::unique_ptr<ExprAST> Step;
    if (CurTok == ',') {
        getNextToken();
        Step = ParseExpression();
        if (!Step)
            return nullptr;
    }

    if (CurTok != tok_in)
        return LogError("expected 'in' after for");
    getNextToken();

    auto Body = ParseExpression();
    if (!Body)
        return nullptr;
    
    return std::make_unique<ForExprAST>(IdName, std::move(Start), std::move(End), std::move(Step), std::move(Body));
}

/// varexpr ::= 'var' identifier ('=' expression)?
//              (',' identifier ('=' expression)?)* 'in' expression
std::unique_ptr<ExprAST> ParseVarExpr() {
    getNextToken();
    if (CurTok != tok_identifier)
        return LogError("expected identifier after var");

    std::vector<std::pair<std::string, std::unique_ptr<ExprAST>>> VarNames;
    while (true) {
        std::string Name = IdentifierStr;
        std::unique_ptr<ExprAST> Init;
        getNextToken();
        if (CurTok == '=') {
            getNextToken();
            Init = ParseExpression();
            if (!Init)
                return nullptr;
        }
        VarNames.push_back(std::make_pair(Name, std::move(Init)));

        if (CurTok != ',')
            break;
     
        getNextToken();
        if (CurTok != tok_identifier)
            return LogError("expected identifier list after var");
    }

    if (CurTok != tok_in)
        return LogError("expected 'in' keyword after var");
    getNextToken();

    auto Body = ParseExpression();
    if (!Body)
        return nullptr;

    return std::make_unique<VarExprAST>(std::move(VarNames), std::move(Body));
}

/// primary
///   ::= identifierexpr
///   ::= numberexpr
///   ::= parenexpr
///   ::= ifexpr
///   ::= forexpr
///   ::= varexpr
static std::unique_ptr<ExprAST> ParsePrimary() {
    switch (CurTok) {
        case tok_number:
            return ParseNumberExpr();
        case tok_identifier:
            return ParseIdentifierExpr();
        case '(':
            return ParseParenExpr();
        case tok_if:
            return ParseIfExpr();
        case tok_for:
            return ParseForExpr();
        case tok_var:
            return ParseVarExpr();
        default:
            return LogError("unknown token when expecting an expression");
    }
}

/// unary
///   ::= primary
///   ::= '!' unary
static std::unique_ptr<ExprAST> ParseUnary() {
    // If the current token is not an operator, it must be a primary expr.
    if (!isascii(CurTok) || CurTok == '(' || CurTok == ',')
        return ParsePrimary();
    
    // If this is a unary operator, read it.
    char Op = (char)CurTok;
    getNextToken();
    if (auto Operand = ParseUnary())
        return std::make_unique<UnaryExprAST>(Op, std::move(Operand));
    return nullptr;
}

/// binoprhs
///   ::= ('+' unary)*
static std::unique_ptr<ExprAST> ParseBinOpRHS(int ExprPrec, std::unique_ptr<ExprAST> LHS) {
    while (true) {
        int TokPrec = GetTokPrecedence();
        if (TokPrec <= ExprPrec)
            return LHS;
        int BinOp = CurTok;
        SourceLocation BinLoc = CurLoc;
        getNextToken();
        auto RHS = ParseUnary();
        if (!RHS)
            return nullptr; // Why do we need to return a nullptr instead of reporting an error? Because we have reported the error when parse RHS.
        int NextPrec = GetTokPrecedence();
        if (TokPrec < NextPrec) {
            RHS = ParseBinOpRHS(TokPrec, std::move(RHS));
            if (!RHS)
                return nullptr; // Why do we need to return a nullptr instead of reporting an error? Because we have reported the error when parse RHS.
        }
        LHS = std::make_unique<BinaryExprAST>(BinLoc, BinOp, std::move(LHS), std::move(RHS));
    }
}

/// expression
///   ::= unary binoprhs
static std::unique_ptr<ExprAST> ParseExpression() {
    auto LHS = ParseUnary();
    if (!LHS)
        return nullptr;
    return ParseBinOpRHS(0, std::move(LHS));
}

/// prototype
///   ::= id '(' id* ')'
///   ::= unary LETTER (id)
///   ::= binary LETTER numbers? (id, id)
static std::unique_ptr<PrototypeAST> ParsePrototype() {
    std::string FnName;

    SourceLocation FnLoc = CurLoc;

    unsigned Kind = 0; // 0 = identifier, 1 = unary, 2 = binary.
    unsigned BinaryPrecedence = 30;

    switch (CurTok) {
        default:
            return LogErrorP("Expected function name in prototype");
        case tok_identifier:
            FnName = IdentifierStr;
            Kind = 0;
            getNextToken();
            break;
        case tok_unary:
            getNextToken();
            if (!isascii(CurTok))
                return LogErrorP("Expected unary operator");
            FnName = "unary";
            FnName += (char)CurTok;
            Kind = 1;
            getNextToken();
            break;    
        case tok_binary:
            getNextToken();
            if (!isascii(CurTok))
                return LogErrorP("Expected binary operator");
            FnName = "binary";
            FnName += (char)CurTok;
            Kind = 2;
            getNextToken();
            if (CurTok == tok_number) {
                if (NumVal < 1 || NumVal > 100)
                    return LogErrorP("Invalid precedence: must be 1...100");
                BinaryPrecedence = NumVal;
                getNextToken();
            }
            break;
    }

    if (CurTok != '(')
        return LogErrorP("Expected '(' in prototype");

    // Read the list of argument names.
    std::vector<std::string> Args;
    while (getNextToken() == tok_identifier)
        Args.push_back(IdentifierStr);
    if (CurTok != ')')
        return LogErrorP("Expected ')' in prototype");
    // success.
    getNextToken(); // eat ')'.

    // Verify right number of names for operator.
    if (Kind && Args.size() != Kind)
        LogErrorP("Invalid number of operands of operator");

    return std::make_unique<PrototypeAST>(FnLoc, FnName, Args, Kind != 0, BinaryPrecedence);
}

/// definition ::= 'def' prototype expression
static std::unique_ptr<FunctionAST> ParseDefinition() {
    getNextToken();  // eat def.
    auto Proto = ParsePrototype();
    if (!Proto) return nullptr;
    auto E = ParseExpression();
    if (!E) return nullptr;
    return std::make_unique<FunctionAST>(std::move(Proto), std::move(E));
}

/// toplevelexpr ::= expression
static std::unique_ptr<FunctionAST> ParseTopLevelExpr() {
    SourceLocation FnLoc = CurLoc;
    if (auto E = ParseExpression()) {
        // Make an anonymous proto.
        auto Proto = std::make_unique<PrototypeAST>(FnLoc, "main", std::vector<std::string>());
        return std::make_unique<FunctionAST>(std::move(Proto), std::move(E));
    }
    return nullptr;
}

/// external ::= 'extern' prototype
static std::unique_ptr<PrototypeAST> ParseExtern() {
    getNextToken(); // eat extern.
    return ParsePrototype();
}

//===----------------------------------------------------------------------===//
// Code Generation Globals
//===----------------------------------------------------------------------===//

static std::unique_ptr<LLVMContext> TheContext;
static std::unique_ptr<Module> TheModule;
static std::unique_ptr<IRBuilder<>> Builder;
static std::map<std::string, AllocaInst*> NamedValues;
static std::unique_ptr<KaleidoscopeJIT> TheJIT;
static std::map<std::string, std::unique_ptr<PrototypeAST>> FunctionProtos;
static ExitOnError ExitOnErr;

//===----------------------------------------------------------------------===//
// Debug Info Support
//===----------------------------------------------------------------------===//

static std::unique_ptr<DIBuilder> DBuilder;

DIType *DebugInfo::getDoubleTy() {
    if (DblTy)
        return DblTy;
    DblTy = DBuilder->createBasicType("double", 64, dwarf::DW_ATE_float);
    return DblTy;     
}

void DebugInfo::emitLocation(ExprAST *AST) {
    if (!AST)
        return Builder->SetCurrentDebugLocation(DebugLoc());
    DIScope *Scope;
    if (LexicalBlocks.empty())
        Scope = TheCU;
    else
        Scope = LexicalBlocks.back();
    Builder->SetCurrentDebugLocation(DILocation::get(Scope->getContext(), 
        AST->getLine(), AST->getCol(), Scope));
}

static DISubroutineType *CreateFunctionType(unsigned NumArgs) {
    SmallVector<Metadata*, 8> EltTys;
    DIType *DblTy = KSDbgInfo.getDoubleTy();

    // Add the result type.
    EltTys.push_back(DblTy);

    for (unsigned i = 0, e = NumArgs; i != e; ++i)
        EltTys.push_back(DblTy);

    return DBuilder->createSubroutineType(DBuilder->getOrCreateTypeArray(EltTys));
}

//===----------------------------------------------------------------------===//
// Code Generation
//===----------------------------------------------------------------------===//

Value *LogErrorV(const char *Str) {
    LogError(Str);
    return nullptr;
}

Function *getFunction(std::string Name) {
    // First, see if the function has already been added to the current module.
    if (auto F = TheModule->getFunction(Name))
        return F;

    // If not, check whether we can codegen the declaration from some existing
    // prototype.    
    auto FI = FunctionProtos.find(Name);
    if (FI != FunctionProtos.end())
        return FI->second->codegen();

    // If no existing prototype exists, return null.
    return nullptr;
}

/// CreateEntryBlockAlloca - Create an alloca instruction in the entry block of
/// the function.  This is used for mutable variables etc.
static AllocaInst *CreateEntryBlockAlloca(Function *TheFunction, StringRef VarName) {
    IRBuilder<> TmpB(&TheFunction->getEntryBlock(), TheFunction->getEntryBlock().begin());
    return TmpB.CreateAlloca(Type::getDoubleTy(*TheContext), nullptr, VarName);
}

Value *NumberExprAST::codegen() {
    KSDbgInfo.emitLocation(this);
    return ConstantFP::get(*TheContext, APFloat(Val));
}

Value *VariableExprAST::codegen() {
    // Look the variable up in the function.
    AllocaInst *A = NamedValues[Name];
    if (!A)
        return LogErrorV("Unknown variable name");
    KSDbgInfo.emitLocation(this);
    return Builder->CreateLoad(A->getAllocatedType(), A, Name.c_str());
}

Value *UnaryExprAST::codegen() {
    Value *OperandV = Operand->codegen();
    if (!OperandV)
        return nullptr;

    Function *F = getFunction(std::string("unary") + Opcode);
    if (!F)
        return LogErrorV("Unknown unary operator");
    KSDbgInfo.emitLocation(this);
    return Builder->CreateCall(F, OperandV, "unop"); 
}

Value *BinaryExprAST::codegen() {
    KSDbgInfo.emitLocation(this);

    // Special case '=' because we don't want to emit the LHS as an expression.
    if (Opcode == '=') {
        // Assignment requires the LHS to be an identifier.
        // This assume we're building without RTTI because LLVM builds that way by
        // default.  If you build LLVM with RTTI this can be changed to a
        // dynamic_cast for automatic error checking.
        VariableExprAST *LHSE = static_cast<VariableExprAST*>(LHS.get());
        if (!LHSE)
            return LogErrorV("destination of '=' must be a variable");
        Value *Val = RHS->codegen();
        if (!Val)
            return nullptr;
        // Look up the name.
        Value *Variable = NamedValues[LHSE->getName()];
        if (!Variable)
            return LogErrorV("Unknown variable name");
        Builder->CreateStore(Val, Variable);
        return Val;
    }

    Value *L = LHS->codegen();
    Value *R = RHS->codegen();
    if (!L || !R)
        return nullptr;
    switch (Opcode) {
        case '+':
            return Builder->CreateFAdd(L, R, "addtmp");
        case '-':
            return Builder->CreateFSub(L, R, "subtmp");
        case '*':
            return Builder->CreateFMul(L, R, "multmp");
        case '<':
            L = Builder->CreateFCmpULT(L, R, "cmptmp");
            return Builder->CreateUIToFP(L, Type::getDoubleTy(*TheContext), "booltmp");
        default:
            break;  
    }

    Function *F = getFunction(std::string("binary") + Opcode);
    if (!F)
        return LogErrorV("Unknown binary operator");
    Value *Ops[2] = {L, R};
    return Builder->CreateCall(F, Ops, "binop");
}

Value *CallExprAST::codegen() {
    KSDbgInfo.emitLocation(this);

    // Look up the name in the global module table.
    Function *CalleeF = getFunction(Callee);
    if (!CalleeF)
        return LogErrorV("Unknown function referenced");
    
    // If argument mismatch error.
    if (CalleeF->arg_size() != Args.size())
        return LogErrorV("Incorrect # arguments passed");

    std::vector<Value*> ArgsV;
    for (int i = 0, e = Args.size(); i != e; ++i) {
        ArgsV.push_back(Args[i]->codegen());
        if (!ArgsV.back())
            return nullptr;
    }
    return Builder->CreateCall(CalleeF, ArgsV, "calltmp");
}

Value *IfExprAST::codegen() {
    KSDbgInfo.emitLocation(this);

    auto CondV = Cond->codegen();
    if (!CondV)
        return nullptr;

    // Convert condition to a bool by comparing non-equal to 0.0.
    CondV = Builder->CreateFCmpONE(CondV, ConstantFP::get(*TheContext, APFloat(0.0)), "ifcond");

    Function *TheFunction = Builder->GetInsertBlock()->getParent();

    // Create blocks for the then and else cases.  Insert the 'then' block at the
    // end of the function.
    BasicBlock *ThenBB = BasicBlock::Create(*TheContext, "then", TheFunction);
    BasicBlock *ElseBB = BasicBlock::Create(*TheContext, "else");
    BasicBlock *MergeBB = BasicBlock::Create(*TheContext, "ifcont");

    Builder->CreateCondBr(CondV, ThenBB, ElseBB);

    // Emit then value.
    Builder->SetInsertPoint(ThenBB);

    auto ThenV = Then->codegen();
    if (!ThenV)
        return nullptr;

    Builder->CreateBr(MergeBB);
    // Codegen of 'Then' can change the current block, update ThenBB for the PHI.
    // TODO: Which step modifies the value of ThenBB?
    ThenBB = Builder->GetInsertBlock();

    // Emit then value.
    TheFunction->insert(TheFunction->end(), ElseBB);
    Builder->SetInsertPoint(ElseBB);

    auto ElseV = Else->codegen();
    if (!ElseV)
        return nullptr;

    Builder->CreateBr(MergeBB);
    // Codegen of 'Else' can change the current block, update ElseBB for the PHI.
    // TODO: Which step modifies the value of ElseBB?
    ElseBB = Builder->GetInsertBlock();

    // Emit merge block.
    TheFunction->insert(TheFunction->end(), MergeBB);
    Builder->SetInsertPoint(MergeBB);
    PHINode *PN = Builder->CreatePHI(Type::getDoubleTy(*TheContext), 2, "iftmp");
    PN->addIncoming(ThenV, ThenBB);
    PN->addIncoming(ElseV, ElseBB);

    return PN;
}

// Output for-loop as:
//   var = alloca double
//   ...
//   start = startexpr
//   store start -> var
//   goto loop
// loop:
//   endcond = endexpr
//   br endcond, loopbody, afterloop
// loopbody:
//   bodyexpr
//   step = stepexpr
//   curval = load var
//   nextvar = curval + step
//   store nextvar -> var
//   goto loop
// afterloop:
Value *ForExprAST::codegen() {
    Function *TheFunction = Builder->GetInsertBlock()->getParent();

    // Create an alloca for the variable in the entry block.
    AllocaInst *Alloca = CreateEntryBlockAlloca(TheFunction, VarName);

    KSDbgInfo.emitLocation(this);

    // Emit the start code first, without 'variable' in scope.
    Value *StartVal = Start->codegen();
    if (!StartVal)
        return nullptr;

    // Store the value into the alloca.
    Builder->CreateStore(StartVal, Alloca);

    // Make the new basic block for the loop header, inserting after current block.
    BasicBlock *LoopBB = BasicBlock::Create(*TheContext, "loop", TheFunction);
    // Insert an explicit fall through from the current block to the LoopBB.
    Builder->CreateBr(LoopBB);
    // Start insertion in LoopBB.
    Builder->SetInsertPoint(LoopBB);

    // Within the loop, the variable is defined equal to the PHI node.  If it
    // shadows an existing variable, we have to restore it, so save it now.
    AllocaInst *OldVal = NamedValues[VarName];
    NamedValues[VarName] = Alloca;

    // Compute the end condition.
    Value *EndCond = End->codegen();
    if (!EndCond)
        return nullptr;

    // Convert condition to a bool by comparing non-equal to 0.0.
    EndCond = Builder->CreateFCmpONE(EndCond, 
        ConstantFP::get(*TheContext, APFloat(0.0)), "loopcond");

    // Insert the conditional branch into the end of LoopEndBB.
    BasicBlock *LoopBodyBB = BasicBlock::Create(*TheContext, "loopbody", TheFunction);
    BasicBlock *AfterBB = BasicBlock::Create(*TheContext, "afterloop");
    Builder->CreateCondBr(EndCond, LoopBodyBB, AfterBB);

    Builder->SetInsertPoint(LoopBodyBB);

    // Emit the body of the loop.  This, like any other expr, can change the
    // current BB.  Note that we ignore the value computed by the body, but don't
    // allow an error.
    if (!Body->codegen())
        return nullptr;

    // Emit the step value.
    Value *StepVal = nullptr;
    if (Step) {
        StepVal = Step->codegen();
        if (!StepVal)
            return nullptr;
    } else {
        // If not specified, use 1.0.
        StepVal = ConstantFP::get(*TheContext, APFloat(1.0));
    }

    // Reload, increment, and restore the alloca.  This handles the case where
    // the body of the loop mutates the variable.
    Value *CurVal = Builder->CreateLoad(Alloca->getAllocatedType(), Alloca, VarName.c_str());
    Value *NextVal = Builder->CreateFAdd(CurVal, StepVal, "nextval");
    Builder->CreateStore(NextVal, Alloca);

    Builder->CreateBr(LoopBB);

    TheFunction->insert(TheFunction->end(), AfterBB);
    Builder->SetInsertPoint(AfterBB);

    // Restore the unshadowed variable. 
    if (OldVal)
        NamedValues[VarName] = OldVal;
    else
        NamedValues.erase(VarName);

    // for expr always returns 0.0.
    return Constant::getNullValue(Type::getDoubleTy(*TheContext));
}

Value *VarExprAST::codegen() {
    std::vector<std::pair<std::string, AllocaInst*>> OldBindings;
    Function *TheFunction = Builder->GetInsertBlock()->getParent();
    // Register all variables and emit their initializer.
    for (unsigned i = 0, e = VarNames.size(); i != e; ++i) {
        auto &VarName = VarNames[i].first;
        ExprAST *Init = VarNames[i].second.get();
        // Emit the initializer before adding the variable to scope, this prevents
        // the initializer from referencing the variable itself, and permits stuff
        // like this:
        //  var a = 1 in
        //    var a = a in ...   # refers to outer 'a'.
        Value *InitVal;
        if (Init) {
            InitVal = Init->codegen();
            if (!InitVal)
                return nullptr;
        } else {
            InitVal = ConstantFP::get(*TheContext, APFloat(0.0));
        }
        AllocaInst *Alloca = CreateEntryBlockAlloca(TheFunction, VarName);
        Builder->CreateStore(InitVal, Alloca);

        // Remember the old variable binding so that we can restore the binding when
        // we unrecurse.
        if (NamedValues.count(VarName))
            OldBindings.push_back(std::make_pair(VarName, NamedValues[VarName]));

        NamedValues[VarName] = Alloca;
    }

    KSDbgInfo.emitLocation(this);

    Value *BodyVal = Body->codegen();
    if (!BodyVal)
        return nullptr;

    for (const auto [Name, V] : OldBindings)
        NamedValues[Name] = V;

    return BodyVal;
}

Function *PrototypeAST::codegen() {
    // Make the function type:  double(double,double) etc.
    std::vector<Type*> Doubles(Args.size(), Type::getDoubleTy(*TheContext));
    FunctionType *FT = FunctionType::get(Type::getDoubleTy(*TheContext), Doubles, false);
    Function *F = Function::Create(FT, Function::ExternalLinkage, Name, TheModule.get());

    // Set names for all arguments.
    unsigned idx = 0;
    for (auto &arg : F->args())
        arg.setName(Args[idx++]);

    return F;
}

Function *FunctionAST::codegen() {
    // First, check for an existing function from a previous 'extern' declaration.
    auto &P = *Proto;
    FunctionProtos[Proto->getName()] = std::move(Proto);
    Function *TheFunction = getFunction(P.getName());
    if (!TheFunction)
        return nullptr;

    // Modify arguement names in the function prototype to be consistent with the
    // function defination. 
    auto iter = TheFunction->args().begin();
    for (int i = 0, e = P.Args.size(); i != e; ++i, ++iter) {
        if (P.Args[i] != iter->getName())
            iter->setName(P.Args[i]);
    }

    // If this is an operator, install it.
    if (P.isBinaryOp())
        BinopPrecedence[P.getOperatorName()] = P.getBinaryPrecedence();

    // Create a new basic block to start insertion into.
    BasicBlock *BB = BasicBlock::Create(*TheContext, "entry", TheFunction);
    Builder->SetInsertPoint(BB);

    // Create a subprogram DIE for this function.
    DIFile *Unit = DBuilder->createFile(KSDbgInfo.TheCU->getFilename(), 
        KSDbgInfo.TheCU->getDirectory());
    DIScope *FContext = Unit;
    unsigned LineNo = P.getLine();
    unsigned ScopeLine = LineNo;
    DISubprogram *SP = DBuilder->createFunction(FContext, P.getName(), StringRef(), 
        Unit, LineNo, CreateFunctionType(TheFunction->arg_size()), ScopeLine, 
        DINode::FlagPrototyped, DISubprogram::SPFlagDefinition);
    TheFunction->setSubprogram(SP);

    // Push the current scope.
    KSDbgInfo.LexicalBlocks.push_back(SP);
    // Unset the location for the prologue emission (leading instructions with no
    // location in a function are considered part of the prologue and the debugger
    // will run past them when breaking on a function)
    KSDbgInfo.emitLocation(nullptr);

    // Record the function arguments in the NamedValues map.
    NamedValues.clear();
    unsigned ArgIdx = 0;
    for (auto &Arg : TheFunction->args()) {
         // Create an alloca for this variable.
        AllocaInst *Alloca = CreateEntryBlockAlloca(TheFunction, Arg.getName());

        // Create a debug descriptor for the variable.
        DILocalVariable *D = DBuilder->createParameterVariable(SP, Arg.getName(), ++ArgIdx,
            Unit, LineNo, KSDbgInfo.getDoubleTy(), true);
        DBuilder->insertDeclare(Alloca, D, DBuilder->createExpression(), 
            DILocation::get(SP->getContext(), LineNo, 0, SP),
            Builder->GetInsertBlock());

        // Store the initial value into the alloca.
        Builder->CreateStore(&Arg, Alloca);
        // Add arguments to variable symbol table.
        NamedValues[std::string(Arg.getName())] = Alloca;
    }

    KSDbgInfo.emitLocation(Body.get());

    if (Value *RetVal = Body->codegen()) {
        // Finish off the function.
        Builder->CreateRet(RetVal);
        
        // Pop off the lexical block for the function.
        KSDbgInfo.LexicalBlocks.pop_back();

        // Validate the generated code, checking for consistency.
        verifyFunction(*TheFunction);
        return TheFunction;
    }

    // Error reading body, remove function.
    TheFunction->eraseFromParent();

    if (P.isBinaryOp())
        BinopPrecedence.erase(Proto->getOperatorName());

    // Pop off the lexical block for the function since we added it unconditionally.
    KSDbgInfo.LexicalBlocks.pop_back();

    return nullptr;
}

//===----------------------------------------------------------------------===//
// Top-Level parsing and JIT Driver
//===----------------------------------------------------------------------===//

static void InitializeModule() {
    // Open a new context and module.
    TheContext = std::make_unique<LLVMContext>();
    TheModule = std::make_unique<Module>("my cool jit", *TheContext);
    TheModule->setDataLayout(TheJIT->getDataLayout());
    
    // Create a new builder for the module. 
    Builder = std::make_unique<IRBuilder<>>(*TheContext);
}

static void HandleDefinition() {
    if (auto FnAST = ParseDefinition()) {
        if (!FnAST->codegen())
            fprintf(stderr, "Error reading function definition\n");
    } else {
        // Skip token for error recovery.
        getNextToken();
    }
}

static void HandleExtern() {
    if (auto ProtoAST = ParseExtern()) {
        if (!ProtoAST->codegen()) {
            fprintf(stderr, "Error reading extern\n");
        } else {
            FunctionProtos[ProtoAST->getName()] = std::move(ProtoAST);
        }
    } else {
        // Skip token for error recovery.
        getNextToken();
    }
}

static void HandleTopLevelExpression() {
    // Evaluate a top-level expression into an anonymous function.
    if (auto FnAST =  ParseTopLevelExpr()) {
        if (!FnAST->codegen())
            fprintf(stderr, "Error generating code for top level expr"); 
    } else {
        // Skip token for error recovery.
        getNextToken();
    }
}

/// top ::= definition | external | expression | ';'
static void MainLoop() {
    while (true) {
        switch (CurTok) {
            case tok_eof:
                return;
            case ';': // ignore top-level semicolons.
                getNextToken();
                break;
            case tok_def:
                HandleDefinition();
                break;
            case tok_extern:
                HandleExtern();
                break;
            default:
                HandleTopLevelExpression();
                break;
        }  
    }
}

//===----------------------------------------------------------------------===//
// "Library" functions that can be "extern'd" from user code.
//===----------------------------------------------------------------------===//

#ifdef _WIN32
#define DLLEXPORT __declspec(dllexport)
#else
#define DLLEXPORT
#endif

/// putchard - putchar that takes a double and returns 0.
extern "C" DLLEXPORT double putchard(double X) {
    fputc((char)X, stderr);
    // fprintf(stderr, "\n");
    return 0;
}

/// printd - printf that takes a double prints it as "%f\n", returning 0.
extern "C" DLLEXPORT double printd(double X) {
    fprintf(stderr, "%f\n", X);
    return 0;
}

//===----------------------------------------------------------------------===//
// Main driver code.
//===----------------------------------------------------------------------===//

int main() {
    InitializeNativeTarget();
    InitializeNativeTargetAsmPrinter();
    InitializeNativeTargetAsmParser();

    // Install standard binary operators.
    // 1 is lowest precedence.
    BinopPrecedence['='] = 2;
    BinopPrecedence['<'] = 10;
    BinopPrecedence['+'] = 20;
    BinopPrecedence['-'] = 20;
    BinopPrecedence['*'] = 40; // highest.

    // Prime the first token.
    getNextToken();

    TheJIT = ExitOnErr(KaleidoscopeJIT::Create());
    InitializeModule();

    // Add the current debug info version into the module.
    TheModule->addModuleFlag(Module::Warning, "Debug Info Version", DEBUG_METADATA_VERSION);

    // Darwin only supports dwarf2.
    if (Triple(sys::getProcessTriple()).isOSDarwin())
        TheModule->addModuleFlag(llvm::Module::Warning, "Dwarf Version", 2);
    
    // Construct the DIBuilder, we do this here because we need the module.
    DBuilder = std::make_unique<DIBuilder>(*TheModule);

    // Create the compile unit for the module.
    // Currently down as "fib.ks" as a filename since we're redirecting stdin
    // but we'd like actual source locations.
    KSDbgInfo.TheCU = DBuilder->createCompileUnit(dwarf::DW_LANG_C, 
        DBuilder->createFile("fib.ks", "."), "Kaleidoscope Compiler", 
        false, "", 0);

    // Run the main "interpreter loop" now.
    MainLoop();

    // Finalize the debug info.
    DBuilder->finalize();

    // Print out all of the generated code.
    TheModule->print(errs(), nullptr);

    return 0;
}