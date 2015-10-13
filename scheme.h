//注释者：xuegang (qq:308821698 blog: http://www.cppblog.com/flysnowxg)
//原始代码：http://tinyscheme.sourceforge.net/home.html
#pragma once
#include <stdio.h>
#pragma warning(disable:4996)

struct cell_t;
struct scheme;

struct num_t {
	bool is_fix;//是否是整数
	union {
		long i;//整数
		double f;//浮点数
	};
} ;

struct string_t{
	char *_str;
	int _len;
};

typedef cell_t* (*foreign_func_t)(scheme *, cell_t*); //外部的扩展函数原型

struct pait_t{
	struct cell_t *_car;
	struct cell_t *_cdr;
};

enum e_port_subclass {
	port_free=0,
	port_file=1,
	port_string=2,
	port_can_realloc=4,
	port_input=16,
	port_output=32,
	port_eof=64
};

struct port_t {
	unsigned char kind;
	union {
		struct {
			FILE *file;
			char *filename;
			int curr_line;
			int closeit;
		} f;
		struct {
			char *start;
			char *end;//位于最后一个字符之后
			char *curr;
		}s;
	};
};

struct cell_t {
	unsigned int _flag;
	union {
		num_t _num;
		string_t _string;
		foreign_func_t _fun;
		pait_t _pair;
		port_t *_port;
	};
};

#define CELL_SEGSIZE 5000		/* # of cells in one segment */
#define CELL_NSEGMENT 100    /* # of segments for cells */
#define MAX_FILES 256
#define STR_BUFF_SIZE 1024

typedef void * (*func_alloc)(size_t);
typedef void (*func_dealloc)(void *);

struct scheme {
	//内存分配管理
	func_alloc malloc;
	func_dealloc free;
	cell_t* cell_seg[CELL_NSEGMENT];
	int last_cell_seg;
	cell_t* free_cell;				/* cell* to top of free cells */
	long free_cell_count;		/* # of free cells */

	//端口管理
	cell_t* outport;
	cell_t* inport;
	cell_t* save_inport;
	cell_t* loadport;
	port_t load_stack[MAX_FILES];		//我们可能会递归的加载文件或字符串代码 (load "xx.ss") ,这里保存了递归加载的文件时形成的栈
	int nesting_stack[MAX_FILES];		//缓存了访问每个文件时表达式的递归层次
	int top_file_index;

	/* We use 4 registers. */
	int op;							//当前处理方法
	cell_t* args;					/* register for arguments of function */
	cell_t* envir;					/* stack register for current environment */ 
	cell_t* code;					/* register for current code */
	cell_t* call_stack;			/* stack register for next evaluation */
	cell_t* ret_value;
	int nesting;

	cell_t* oblist;				/* cell* to symbol table */		//管理所有的符号，确保了所有相同名字的符号是同一个
	cell_t* global_env;		/* cell* to global environment */

	int tok;						//保持词法分析获取的单词
	char strbuff[STR_BUFF_SIZE];
	int eval_result;			//整个解释器的运行状态 ，解释器退出后，可以通过这个值知道解释器退出的原因
	int print_flag;			//控制atom2str函数中打印输出的格式
	char gc_verbose;      /* if gc_verbose is not zero, print gc status */

	/* global cell*s to special symbols */
	cell_t* sym_lambda;			/* cell* to syntax lambda */
	cell_t* sym_quote;				/* cell* to syntax quote */						//引用    '
	cell_t* sym_qquote;			/* cell* to symbol quasiquote */			//准引用 `
	cell_t* sym_unquote;			/* cell* to symbol unquote */				//解引用 ,
	cell_t* sym_unquote_sp;	/* cell* to symbol unquote-splicing */	//解引用 ,@
	cell_t* sym_feed_to;			/* => */												// cond中有用到
	cell_t* sym_colon_hook;		/* *colon-hook* */
	cell_t* sym_error_hook;		/* *error-hook* */
	cell_t* sym_sharp_hook;		/* *sharp-hook* */
	cell_t* sym_compile_hook;	/* *compile-hook* */
};

/* operator code */
enum opcode {
#define _OP_DEF(A,B,C,D,E,OP) OP,
#include "opdefines.h"
	OP_MAXDEFINED
};

typedef cell_t* (*dispatch_func_t)(scheme *, opcode);
typedef struct {
	dispatch_func_t func;	//函数过程
	char *name;					//函数名
	int min_arity;					//最少参数个数
	int max_arity;				//最大参数个数
	char *args_type;
} op_code_info;
