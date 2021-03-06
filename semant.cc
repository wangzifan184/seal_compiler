#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>
#include "semant.h"
#include "utilities.h"

extern int semant_debug;
extern char *curr_filename;

static ostream& error_stream = cerr;
static int semant_errors = 0;
static Decl curr_decl = 0;

typedef SymbolTable<Symbol, Symbol> ObjectEnvironment; // name, type
ObjectEnvironment objectEnv;


//typedef SymbolTable<Symbol, Decl_class> Call_table;
//Call_table call_table;

typedef std::map<Symbol, Decl> Call_table;
Call_table call_table;

int inloop = 0;
int inif = 0;
bool returnflag = false;


///////////////////////////////////////////////
// helper func
///////////////////////////////////////////////


static ostream& semant_error() {
    semant_errors++;
    return error_stream;
}

static ostream& semant_error(tree_node *t) {
    error_stream << t->get_line_number() << ": ";
    return semant_error();
}

static ostream& internal_error(int lineno) {
    error_stream << "FATAL:" << lineno << ": ";
    return error_stream;
}

//////////////////////////////////////////////////////////////////////
//
// Symbols
//
// For convenience, a large number of symbols are predefined here.
// These symbols include the primitive type and method names, as well
// as fixed names used by the runtime system.
//
//////////////////////////////////////////////////////////////////////

static Symbol 
    Int,
    Float,
    String,
    Bool,
    Void,
    Main,
    print
    ;


bool isValidCallName(Symbol type) {
    return type != (Symbol)print;
}

bool isValidTypeName(Symbol type) {
    return type != Void;
}

//
// Initializing the predefined symbols.
//

static void initialize_constants(void) {
    // 4 basic types and Void type
    Bool        = idtable.add_string("Bool");
    Int         = idtable.add_string("Int");
    String      = idtable.add_string("String");
    Float       = idtable.add_string("Float");
    Void        = idtable.add_string("Void");  
    // Main function
    Main        = idtable.add_string("main");

    // classical function to print things, so defined here for call.
    print        = idtable.add_string("printf");
}

/*
    TODO :
    you should fill the following function defines, so that semant() can realize a semantic 
    analysis in a recursive way. 
    Of course, you can add any other functions to help.
*/

static bool sameType(Symbol name1, Symbol name2) {
    return strcmp(name1->get_string(), name2->get_string()) == 0;
}

static void install_calls(Decls decls) {
	
	
	for (int i=decls->first(); decls->more(i); i=decls->next(i)) {
		if (decls->nth(i)->isCallDecl()) {
			Symbol call_name = decls->nth(i)->getName();
			if (call_table.find(call_name) != call_table.end()) {
				semant_error(decls->nth(i)) << "Function " << decls->nth(i)->getName() <<" was previously defined." << std::endl;
			}
			else if (call_name == print) {
				semant_error(decls->nth(i)) << "Function printf cannot be redefination." << std::endl;
			}
			else {
				call_table.insert(std::make_pair(call_name, decls->nth(i)));
			}
		}
	}
}

static void install_globalVars(Decls decls) {
	
	objectEnv.enterscope();
	for (int i=decls->first(); decls->more(i); i=decls->next(i)) {
		if (!decls->nth(i)->isCallDecl()) {
			if (objectEnv.probe(decls->nth(i)->getName()) != NULL) {
				semant_error(decls->nth(i)) << "var " << decls->nth(i)->getName() << " was previously defined." << endl;
			}
			else if (sameType(decls->nth(i)->getType(), Void)) {
				semant_error(decls->nth(i)) << "var " << decls->nth(i)->getName() << " cannot be of type Void." << endl;
			}
			else if (sameType(decls->nth(i)->getName(), print)) {
				semant_error(decls->nth(i)) << "Variable printf cannot be named printf." << endl;
			}
			else {
				Symbol type = decls->nth(i)->getType();
				objectEnv.addid(decls->nth(i)->getName(), new Symbol(type));
			}
		}
	}
}

static void check_calls(Decls decls) {

	for (int i=decls->first(); decls->more(i); i=decls->next(i)) {
		if (decls->nth(i)->isCallDecl()) {
			
			decls->nth(i)->check();
		}
	}
}

static void check_main() {
	if (call_table.find(Main) == call_table.end()) {
		semant_error() << "Main function is not defined." << std::endl;
	}
}

void VariableDecl_class::check() {
	
	Symbol name = this->getName();
	Symbol type = this->getType();
	if (sameType(type, Void)) {
		semant_error(this) << "var " << this->getName() << " cannot be of type Void. Void can just be used as return type." << std::endl;
	}
}

void CallDecl_class::check() {
	Variables vars = this->getVariables();
	
	objectEnv.enterscope();
	
	for (int i=vars->first(); vars->more(i); i=vars->next(i)) {
		Symbol name = vars->nth(i)->getName();
		
		if (objectEnv.probe(name) != NULL) {
			semant_error(vars->nth(i)) << "Function " << this->getName() << " 's parameter has a duplicate name " << name << "." << std::endl;
		}
		else {
			Symbol vartype = vars->nth(i)->getType();
			objectEnv.addid(name, new Symbol(vartype));
		}
	}
	
	//main() has return type 'void' and no params
	if (sameType(this->getName(), Main)) {
		if (!sameType(this->getType(), Void)) {
			semant_error(this) << "Main function should have return type Void." << std::endl;
		}
		if (vars->len()) {
			semant_error(this) << "Main function should not have any parameters" << std::endl;
		}
	}
	
	this->body->check(this->getType());
	
	objectEnv.exitscope();
	if (!returnflag) {
		semant_error(this) << "Function " << this->getName() << " must have an overall return statement." << std::endl;
	}
	returnflag = false;
}

void StmtBlock_class::check(Symbol type) {

	/*class StmtBlock_class : public Stmt_class {
		protected:
			VariableDecls vars;
			Stmts	stmts;
	*/
	//VariableDecls
	
	VariableDecls var_decls = this->getVariableDecls();
	//check for duplicate variable declarations and add variables to var_scope
	
	for (int i=var_decls->first(); var_decls->more(i); i=var_decls->next(i)) {
		if (objectEnv.probe(var_decls->nth(i)->getName()) != NULL) {
			semant_error(var_decls->nth(i)) << "var " << var_decls->nth(i)->getName() << " was previously defined." << std::endl;
		}
		else {
			Symbol type = var_decls->nth(i)->getType();
			objectEnv.addid(var_decls->nth(i)->getName(), new Symbol(type));
		}
		
		//check variable declarations one by one
		var_decls->nth(i)->check();
	}
	
	//Stmts : list of Stmt
	//this part is unfinished yet. should lookup variables used in stmts in var_scope
	Stmts stmts = this->getStmts();
	for (int i=stmts->first(); stmts->more(i); i=stmts->next(i)) {
		stmts->nth(i)->check(type);
	}
}

void IfStmt_class::check(Symbol type) {

	/*class IfStmt_class : public Stmt_class {
	protected:
		Expr condition;
		StmtBlock thenexpr, elseexpr;
	*/
	this->getCondition()->checkType();
	++inif;
	objectEnv.enterscope();
	this->getThen()->check(type);
	objectEnv.exitscope();
	
	objectEnv.enterscope();
	this->getElse()->check(type);
	objectEnv.exitscope();
	--inif;
}

void WhileStmt_class::check(Symbol type) {

	/*class WhileStmt_class : public Stmt_class {
	protected:
		Expr condition; getCondition()
		StmtBlock body; getBody()
	*/
	this->getCondition()->checkType();
	
	++inloop;
	objectEnv.enterscope();
	this->getBody()->check(type);
	objectEnv.exitscope();
	--inloop;
}

void ForStmt_class::check(Symbol type) {

	/*class ForStmt_class : public Stmt_class {
	protected:
	Expr initexpr, condition, loopact;
	StmtBlock body;	getInit(), getCondition(), getLoop(), getBody()
	*/
	
	this->getInit()->checkType();
	this->getCondition()->checkType();
	this->getLoop()->checkType();

	++inloop;
	objectEnv.enterscope();
	this->getBody()->check(type);
	objectEnv.exitscope();
	--inloop;
}

void ReturnStmt_class::check(Symbol type) {

	/*class ReturnStmt_class : public Stmt_class {
	protected:
	Expr value;  getValue()
	*/
	Symbol exprtype = this->getValue()->checkType();
	
	if (!sameType(type, exprtype)) {
		semant_error(this) << "Returns " << exprtype << " , but need " << type << std::endl;
	}
	if(inif == 0 && inloop == 0) returnflag = true;
}

void ContinueStmt_class::check(Symbol type) {
	if (inloop == 0) {
		semant_error(this) << "continue must be used in a loop sentence." << std::endl;
	}
}

void BreakStmt_class::check(Symbol type) {
	if (inloop == 0) {
		semant_error(this) << "break must be used in a loop sentence." << std::endl;
	}
}

Symbol Call_class::checkType(){
	Symbol name = this->getName();
	Actuals actuals = this->getActuals();
	
	if(sameType(name, print)) {
		if (actuals->len() == 0) {
			semant_error(this) << "printf() must have at least one parameter." << std::endl;
		}
		if (!sameType(actuals->nth(actuals->first())->checkType(), String)) {
			semant_error(this) << "printf()'s first parameter must be of type String." << std::endl;
		}
		return Void;
	}
	else if(call_table.find(name) == call_table.end()) {
		semant_error(this) << "function " << name << " not defined." << std::endl;
		return Void;
	}
	else {
		if (actuals->len() != call_table.find(name)->second->getVariables()->len()) {
			semant_error(this) << "Function " << name <<" called with wrong number of arguments." << std::endl;
		}
		else {
			Variables vars = call_table.find(name)->second->getVariables();
			for(int i=vars->first(); vars->more(i); i=vars->next(i)) {
				Symbol vartype = vars->nth(i)->getType();
				Symbol actualtype = actuals->nth(i)->checkType();
				
				if (!sameType(actualtype, vartype)) {
					semant_error(this) << "type " << actualtype << " of parameter " << vars->nth(i)->getName() << " does not conform to declared type " << vartype << "." << std::endl;
				}
			}
		}
		
	}
	Symbol calltype = call_table.find(name)->second->getType();
	this->setType(calltype);
	return calltype;
}

Symbol Actual_class::checkType(){
	this->setType(expr->checkType());
	return type;
}

Symbol Assign_class::checkType(){

	Symbol valuetype = value->checkType();
	if(objectEnv.lookup(lvalue) == NULL) {
		semant_error(this) << "Left value " << lvalue << " has not been defined." << std::endl;
	}
	else if(!sameType(*(objectEnv.lookup(lvalue)), valuetype)) {
		semant_error(this) << "Right value must have type " << *(objectEnv.lookup(lvalue)) << " , got " << valuetype << std::endl;
	}
	this->setType(valuetype);
	return valuetype;
}

Symbol Add_class::checkType(){

	Symbol type1 = e1->checkType();
	Symbol type2 = e2->checkType();	
	
	if (sameType(type1, Float) && (sameType(type2, Int) || sameType(type2, Float))) {
		type = Float;
	}
	else if (sameType(type2, Float) && (sameType(type1, Int) || sameType(type1, Float))) {
		type = Float;
	}
	else if (sameType(type1, Int) && sameType(type2, Int)) {
		type = Int;
	}
	else {
		semant_error(this) << "Cannot add a " << type1 << " and a " << type2 << "." << std::endl;
		type = Void;
	}
	return type;
}

Symbol Minus_class::checkType(){
	Symbol type1 = e1->checkType();
	Symbol type2 = e2->checkType();	
	
	if (sameType(type1, Float) && (sameType(type2, Int) || sameType(type2, Float))) {
		type = Float;
	}
	else if (sameType(type2, Float) && (sameType(type1, Int) || sameType(type1, Float))) {
		type = Float;
	}
	else if (sameType(type1, Int) && sameType(type2, Int)) {
		type = Int;
	}
	else {
		semant_error(this) << "Cannot minus a " << type1 << " and a " << type2 << "." << std::endl;
		type = Void;
	}
	return type;
}

Symbol Multi_class::checkType(){
	Symbol type1 = e1->checkType();
	Symbol type2 = e2->checkType();	
	
	if (sameType(type1, Float) && (sameType(type2, Int) || sameType(type2, Float))) {
		type = Float;
	}
	else if (sameType(type2, Float) && (sameType(type1, Int) || sameType(type1, Float))) {
		type = Float;
	}
	else if (sameType(type1, Int) && sameType(type2, Int)) {
		type = Int;
	}
	else {
		semant_error(this) << "Cannot multi a " << type1 << " and a " << type2 << "." << std::endl;
		type = Void;
	}
	return type;
}

Symbol Divide_class::checkType(){
	Symbol type1 = e1->checkType();
	Symbol type2 = e2->checkType();	
	
	if (sameType(type1, Float) && (sameType(type2, Int) || sameType(type2, Float))) {
		type = Float;
	}
	else if (sameType(type2, Float) && (sameType(type1, Int) || sameType(type1, Float))) {
		type = Float;
	}
	else if (sameType(type1, Int) && sameType(type2, Int)) {
		type = Int;
	}
	else {
		semant_error(this) << "Cannot div a " << type1 << " and a " << type2 << "." << std::endl;
		type = Void;
	}
	return type;
}

Symbol Mod_class::checkType(){
	Symbol type1 = e1->checkType();
	Symbol type2 = e2->checkType();	
	
	if (sameType(type1, Int) && sameType(type2, Int)) {
		type = Int;
	}
	else {
		semant_error(this) << "Cannot mod a " << type1 << " and a " << type2 << "." << std::endl;
		type = Void;
	}
	return type;
}

Symbol Neg_class::checkType(){
	if(!sameType(e1->getType(), Int) || !sameType(e1->getType(), Float)) {
		semant_error(this) << "A" << e1->getType() <<"doesn't have a negative." << std::endl;
		this->setType(Void);
	}
	
	this->setType(Int);
	return type;
}

Symbol Lt_class::checkType(){
	Symbol type1 = e1->checkType();
	Symbol type2 = e2->checkType();	
	
	if ((sameType(type1, Float) || sameType(type1, Int)) && (sameType(type2, Float) || sameType(type2, Int))) {
		type = Bool;
	}
	else {
		semant_error(this) << "Cannot compare a " << type1 << " and a " << type2 << "." << std::endl;
		type = Void;
	}
	return type;
}

Symbol Le_class::checkType(){
	Symbol type1 = e1->checkType();
	Symbol type2 = e2->checkType();	
	
	if ((sameType(type1, Float) || sameType(type1, Int)) && (sameType(type2, Float) || sameType(type2, Int))) {
		type = Bool;
	}
	else {
		semant_error(this) << "Cannot compare a " << type1 << " and a " << type2 << "." << std::endl;
		type = Void;
	}
	return type;
}

Symbol Equ_class::checkType(){
	Symbol type1 = e1->checkType();
	Symbol type2 = e2->checkType();	
	
	if ((sameType(type1, Float) || sameType(type1, Int) || sameType(type1, Bool)) && (sameType(type2, Float) || sameType(type2, Int) || sameType(type2, Bool))) {
		type = Bool;
	}
	else {
		semant_error(this) << "Cannot compare a " << type1 << " and a " << type2 << "." << std::endl;
		type = Void;
	}
	return type;
}

Symbol Neq_class::checkType(){
	Symbol type1 = e1->checkType();
	Symbol type2 = e2->checkType();	
	
	if ((sameType(type1, Float) || sameType(type1, Int) || sameType(type1, Bool)) && (sameType(type2, Float) || sameType(type2, Int) || sameType(type2, Bool))) {
		type = Bool;
	}
	else {
		semant_error(this) << "Cannot compare a " << type1 << " and a " << type2 << "." << std::endl;
		type = Void;
	}
	return type;
}

Symbol Ge_class::checkType(){
	Symbol type1 = e1->checkType();
	Symbol type2 = e2->checkType();	
	
	if ((sameType(type1, Float) || sameType(type1, Int)) && (sameType(type2, Float) || sameType(type2, Int))) {
		type = Bool;
	}
	else {
		semant_error(this) << "Cannot compare a " << type1 << " and a " << type2 << "." << std::endl;
		type = Void;
	}
	return type;
}

Symbol Gt_class::checkType(){
	Symbol type1 = e1->checkType();
	Symbol type2 = e2->checkType();	
	
	if ((sameType(type1, Float) || sameType(type1, Int)) && (sameType(type2, Float) || sameType(type2, Int))) {
		type = Bool;
	}
	else {
		semant_error(this) << "Cannot compare a " << type1 << " and a " << type2 << "." << std::endl;
		type = Void;
	}
	return type;
}

Symbol And_class::checkType(){
	Symbol type1 = e1->checkType();
	Symbol type2 = e2->checkType();	
	
	if (sameType(type1, Bool) && sameType(type2, Bool)) {
		type = Bool;
	}
	else {
		semant_error(this) << "Cannot use && between " << type1 << " and " << type2 << "." << std::endl;
		type = Void;
	}
	return type;
}

Symbol Or_class::checkType(){
	Symbol type1 = e1->checkType();
	Symbol type2 = e2->checkType();	
	
	if (sameType(type1, Bool) && sameType(type2, Bool)) {
		type = Bool;
	}
	else {
		semant_error(this) << "Cannot use || between " << type1 << " and " << type2 << "." << std::endl;
		type = Void;
	}
	return type;
}

Symbol Xor_class::checkType(){
	Symbol type1 = e1->checkType();
	Symbol type2 = e2->checkType();	
	
	if (sameType(type1, Bool) && sameType(type2, Bool)) {
		type = Bool;
	}
	else {
		semant_error(this) << "Cannot use ^ between " << type1 << " and " << type2 << "." << std::endl;
		type = Void;
	}
	return type;
}

Symbol Not_class::checkType(){
	Symbol type1 = e1->checkType();	
	
	if (sameType(type1, Bool)) {
		type = Bool;
	}
	else {
		semant_error(this) << "Cannot use ! upon " << type1 << "." << std::endl;
		type = Void;
	}
	return type;
}

Symbol Bitand_class::checkType(){
	Symbol type1 = e1->checkType();
	Symbol type2 = e2->checkType();	
	
	if (sameType(type1, Bool) && sameType(type2, Bool)) {
		type = Bool;
	}
	else {
		semant_error(this) << "Cannot use & between " << type1 << " and " << type2 << "." << std::endl;
		type = Void;
	}
	return type;
}

Symbol Bitor_class::checkType(){
	Symbol type1 = e1->checkType();
	Symbol type2 = e2->checkType();	
	
	if (sameType(type1, Bool) && sameType(type2, Bool)) {
		type = Bool;
	}
	else {
		semant_error(this) << "Cannot use | between " << type1 << " and " << type2 << "." << std::endl;
		type = Void;
	}
	return type;
}

Symbol Bitnot_class::checkType(){
	Symbol type1 = e1->checkType();	
	
	if (sameType(type1, Bool)) {
		type = Bool;
	}
	else {
		semant_error(this) << "Cannot use unary op ~ upon " << type1 << "." << std::endl;
		type = Void;
	}
	return type;
}

Symbol Const_int_class::checkType(){
    type = Int;
    return type;
}

Symbol Const_string_class::checkType(){
    type = String;
    return type;
}

Symbol Const_float_class::checkType(){
    type = Float;
    return type;
}

Symbol Const_bool_class::checkType(){
    type = Bool;
    return type;
}

Symbol Object_class::checkType(){

	Symbol obtype;
	if(objectEnv.lookup(var) == NULL) {
		semant_error(this) << "object " << var << " has not been defined." << std::endl;
		obtype = Void;
	}
	else {
		obtype = *(objectEnv.lookup(var));
	}
	this->setType(obtype);
	return obtype;
}

Symbol No_expr_class::checkType(){
    setType(Void);
    return getType();
}

void Program_class::semant() {
    initialize_constants();
    install_calls(decls);
    check_main();
    install_globalVars(decls);
    check_calls(decls);
    
    if (semant_errors > 0) {
        cerr << "Compilation halted due to static semantic errors." << endl;
        exit(1);
    }
}



