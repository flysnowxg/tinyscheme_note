//注释者：xuegang (qq:308821698 blog: http://www.cppblog.com/flysnowxg)
//原始代码：http://tinyscheme.sourceforge.net/home.html
//说明：这个代码是基于tinyscheme-1.41版本的，在阅读这个代码过程中，
//         为了方便阅读对这个代码做了大幅度的修改，并加了很多注释
#include <math.h>
#include <limits.h>
#include <float.h>
#include <ctype.h>
#include <string.h>
#include <stdlib.h>
#include "scheme.h"

static void gc(scheme *sc, cell_t* a, cell_t* b);
static int syntax_sym2opcode(cell_t* p);
cell_t* mk_symbol(scheme *sc, const char *name) ;

#define TOK_EOF     -1					// 输入结束
#define TOK_LPAREN  0				// (
#define TOK_RPAREN  1				// )
#define TOK_DOT     2					// .
#define TOK_ATOM    3				// 原子 （number id symbol ）
#define TOK_QUOTE   4				// ' 
#define TOK_COMMENT 5			// ,
#define TOK_DQUOTE  6				// "
#define TOK_BQUOTE  7				// `
#define TOK_COMMA   8				// ,
#define TOK_ATMARK  9				// ,@
#define TOK_SHARP 10					// # 
#define TOK_SHARP_CONST 11		// #  常量 (例如 #t #f #\a)
#define TOK_VECTOR 12				// #( 数组

#define DELIMITERS  "()\";\f\t\v\n\r "	// 分隔符 
#define BLOCK_SIZE 256

enum scheme_type {
	T_PAIR=1,								// 点对
	T_NUMBER=2,						// 数字
	T_CHAR=3,							// 字符
	T_STRING=4,							// 字符串
	T_SYMBOL=5,						// 符号
	T_VECTOR=6,						// 数组 vector : pair<any,any>[num]
	T_PORT=7,							// 端口
	T_PROC=8,							// 过程
	T_FOREIGN=9,						// 扩展过程
	T_CLOSURE=10,					// 闭包
	T_PROMISE=11,					// 
	T_MACRO=12,						// 宏
	T_CONTINUATION=13,			// 延续
	T_ENVIRONMENT=14,			// 环境 	
	T_LAST_TYPE=14					// 最大编号
};

//													/* 7654321076543210 */	// 16位
#define TYPE_MASK			31			/* 0000000000011111 */	// 5位 可以表示32个类型
#define T_SYNTAX			4096		/* 0001000000000000 */    // 语法符号
#define T_IMMUTABLE		8192		/* 0010000000000000 */	// 标记一个cell为不可改变的
#define T_ATOM				16384	/* 0100000000000000 */	// 标记一个cell为原子
#define REF_MARK			32768	/* 1000000000000000 */	/* only for gc */

/* macros for cell operations */
#define typeflag(p)    ((p)->_flag)
#define type(p)          (typeflag(p)&TYPE_MASK)	//p->_flag低5位是scheme_types类型的信息

#define is_atom(p)       (typeflag(p)&T_ATOM)
#define setatom(p)       typeflag(p) |= T_ATOM
#define clratom(p)       typeflag(p) &= ~T_ATOM

#define is_mark(p)       (typeflag(p)&REF_MARK)
#define setmark(p)       typeflag(p) |= REF_MARK
#define clrmark(p)       typeflag(p) &= ~REF_MARK

cell_t g_sink;
cell_t g_nil;
cell_t g_true;
cell_t g_false;
cell_t g_eof;
#define car(p)           ((p)->_pair._car)
#define cdr(p)           ((p)->_pair._cdr)
#define caar(p)          car(car(p))
#define cadr(p)          car(cdr(p))
#define cdar(p)          cdr(car(p))
#define cddr(p)          cdr(cdr(p))
#define cadar(p)         car(cdr(car(p)))
#define caddr(p)         car(cdr(cdr(p)))
#define cdaar(p)         cdr(car(car(p)))
#define cadaar(p)        car(cdr(car(car(p))))
#define cadddr(p)        car(cdr(cdr(cdr(p))))
#define cddddr(p)        cdr(cdr(cdr(cdr(p))))
int is_pair(cell_t* p)     { return (type(p)==T_PAIR); }
#define cons(sc,a,b) mk_pair(sc,a,b,0)
#define immutable_cons(sc,a,b) mk_pair(sc,a,b,1)

static num_t g_zero;
static num_t g_one;
#define ivalue_unchecked(p)       ((p)->_num.i)
#define num2int(n)       (n.is_fix?(n).i:(long)(n).f)
#define num2float(n)       (!n.is_fix?(n).f:(double)(n).i)
long ivalue(cell_t* p)      {return num2int(p->_num); }//将一个数字转换为整数返回
double rvalue(cell_t* p)    {return num2float(p->_num);}//将一个数字转换为浮点数返回
num_t* inital_num(num_t* self,long i){
	self->is_fix=true;
	self->i=i;
	return self;
}
num_t* inital_num(num_t* self,double f){
	self->is_fix=false;
	self->f=f;
	return self;
}
int is_number(cell_t* p){return (type(p)==T_NUMBER); }//判断是不是数字
int is_integer(cell_t* p){ //判断是不是整数,或者是一个可以无损转换为整数的浮点数
	if (!is_number(p)) return 0;
	if (p->_num.is_fix || (double)ivalue(p) == rvalue(p)) return 1;
	return 0;
}
int is_real(cell_t* p) {return is_number(p) && (!(p)->_num.is_fix);}//判断是不是浮点数
num_t nvalue(cell_t* p) { return ((p)->_num); }//从cell中提取数字

int is_character(cell_t* p) { return (type(p)==T_CHAR); }//判断是不是字符
long char_value(cell_t* p)  { return p->_num.i; }

int is_string(cell_t* p) { return (type(p)==T_STRING); }	//是否是字符串
#define string_value(p) (p)->_string._str	 //获取字符串的值
#define string_len(p)  ((p)->_string._len)	 //字符串的长度

int is_symbol(cell_t* sym)  { return (type(sym)==T_SYMBOL); }//符号: (STRING)
char *sym_name(cell_t* sym)  { return string_value(car(sym)); }
#define sym_value(sym_kv) cdr(sym_kv)

int is_syntax(cell_t* p) { return (typeflag(p)&T_SYNTAX); }

int is_vector(cell_t* p)  { return (type(p)==T_VECTOR); }	// 是否是数组

int is_port(cell_t* p)   { return (type(p)==T_PORT); }
int is_inport(cell_t* p)  { return is_port(p) && p->_port->kind & port_input; }
int is_outport(cell_t* p) { return is_port(p) && p->_port->kind & port_output; }

int is_proc(cell_t* p) { return (type(p)==T_PROC); }
static const char *proc_name(cell_t* x);
#define proc_value(p)  ivalue(p)

int is_foreign(cell_t* p)  { return (type(p)==T_FOREIGN); }

int is_closure(cell_t* p)  { return (type(p)==T_CLOSURE); }
cell_t* closure_code(cell_t* p)   { return car(p); }
cell_t* closure_env(cell_t* p)    { return cdr(p); }

/* To do: promise should be forced ONCE only */
int is_promise(cell_t* p)  { return (type(p)==T_PROMISE); }

int is_macro(cell_t* p)    { return (type(p)==T_MACRO); }

int is_continuation(cell_t* p)    { return (type(p)==T_CONTINUATION); }

int is_environment(cell_t* p) { return (type(p)==T_ENVIRONMENT); }

int is_immutable(cell_t* p) { return (typeflag(p)&T_IMMUTABLE); }
void setimmutable(cell_t* p) { typeflag(p) |= T_IMMUTABLE; }

/* () is #t in R5RS */ //不为#f的都是true
#define is_true(p)       ((p) != &g_false)
#define is_false(p)      ((p) == &g_false)

//一些简单的帮助函数
static  int isalphax(int c) { return isascii(c) && isalpha(c); }//是否是字母
static  int isdigitx(int c) { return isascii(c) && isdigit(c); }//是否是数字
static  int isspacex(int c) { return isascii(c) && isspace(c); }//是否是空格
static  int isupperx(int c) { return isascii(c) && isupper(c); }//是否是大写字母
static  int islowerx(int c) { return isascii(c) && islower(c); }//是否是小写字母

static const char *charnames[32]={
	"nul",
	"soh",
	"stx",
	"etx",
	"eot",
	"enq",
	"ack",
	"bel",
	"bs",
	"ht",
	"lf",
	"vt",
	"ff",
	"cr",
	"so",
	"si",
	"dle",
	"dc1",
	"dc2",
	"dc3",
	"dc4",
	"nak",
	"syn",
	"etb",
	"can",
	"em",
	"sub",
	"esc",
	"fs",
	"gs",
	"rs",
	"us"
};

static int is_ascii_name(const char *name, int *pc) {
	for(int i=0; i<32; i++) {
		if(stricmp(name,charnames[i])==0) {
			*pc=i;
			return 1;
		}
	}
	if(stricmp(name,"del")==0) {
		*pc=127;
		return 1;
	}
	return 0;
}

static int hash_fn(const char *key, int table_size)
{
	unsigned int hashed = 0;
	for (const char *c = key; *c; c++) {
		int bits_per_int = sizeof(unsigned int)*8;
		/* letters have about 5 bits in them */
		hashed = (hashed<<5) | (hashed>>(bits_per_int-5));
		hashed ^= *c;
	}
	return hashed % table_size;
}

/* allocate new cell segment */
static int alloc_cellseg(scheme *sc, int n) {
	for (int k = 0; k < n; k++) {
		if (sc->last_cell_seg >= CELL_NSEGMENT - 1) return k;
		sc->cell_seg[sc->last_cell_seg+1]= (cell_t*) sc->malloc((CELL_SEGSIZE+1) * sizeof(struct cell_t));
		long i = ++sc->last_cell_seg ;
		cell_t* p_new=sc->cell_seg[i];
		while (i > 0 && sc->cell_seg[i - 1] > sc->cell_seg[i]) {//插入排序，sc->cell_seg中的元素安装指针值的从小大排序
			sc->cell_seg[i] = sc->cell_seg[i - 1];
			sc->cell_seg[--i] = p_new;
		}
		sc->free_cell_count += CELL_SEGSIZE;//增加空闲单元的计数
		//所有的空闲cell构成一个链表，并且依照位置值从小到大排列
		cell_t* last = p_new + CELL_SEGSIZE - 1;
		for (cell_t* p = p_new; p <= last; p++) {
			typeflag(p) = 0;
			cdr(p) = p + 1;
			car(p) = &g_nil;
		}
		/* insert new cells in address order on free list */
		if (sc->free_cell == &g_nil || last < sc->free_cell) {
			cdr(last) = sc->free_cell;
			sc->free_cell = p_new;
		} else {
			cell_t* p = sc->free_cell;
			while (cdr(p) != &g_nil && p_new > cdr(p))p = cdr(p);
			cdr(last) = cdr(p);
			cdr(p) = p_new;
		}
	}
	return n;
}

/* get new cell.  parameter a, b is marked by gc. */
static  cell_t* create_cell_helper(scheme *sc, cell_t* a, cell_t* b) {//分配一个cell
	if (sc->free_cell == &g_nil) {
		gc(sc,a, b);
		if (sc->free_cell == &g_nil) {
			if (!alloc_cellseg(sc,1) && sc->free_cell == &g_nil) {
				printf("No Memory ! ! !\n");
				while(true) getchar();
			}
		}
	}
	cell_t* p = sc->free_cell;
	sc->free_cell = cdr(p);
	--sc->free_cell_count;
	return p;
}

static cell_t* mk_cell(scheme *sc, cell_t* a, cell_t* b){
	cell_t* p = create_cell_helper(sc, a, b);
	/* For right now, include "a" and "b" in "cell" so that gc doesn't think they are garbage. */
	/* Tentatively record it as a pair so gc understands it. */
	typeflag(p) = T_PAIR;
	car(p) = a;
	cdr(p) = b;
	return p;
}

static int count_consecutive_cells(cell_t* x, int needed) {
	int n=1;
	while(cdr(x)==x+1) {//如果是连续的cell ， cdr(x)与x+1 必然相等
		x=cdr(x);
		n++;
		if(n>needed) return n;
	}
	return n;
}

static cell_t* find_consecutive_cells(scheme *sc, int n) {
	cell_t* *pp=&sc->free_cell;
	while(*pp!=&g_nil) {
		int cnt=count_consecutive_cells(*pp,n);
		if(cnt>=n) {
			cell_t* x=*pp;
			*pp=cdr(*pp+n-1);
			sc->free_cell_count -= n;
			return x;
		}
		pp=&cdr(*pp+cnt-1);
	}
	return &g_nil;
}

//获取n个连续的cell
static cell_t* get_consecutive_cells(scheme *sc, int n) {
	/* Are there any cells available? */
	cell_t* x=find_consecutive_cells(sc,n);
	if (x != &g_nil)  return x; 

	/* If not, try gc'ing some */
	gc(sc, &g_nil, &g_nil);
	x=find_consecutive_cells(sc,n);
	if (x != &g_nil)  return x; 

	/* If there still aren't, try getting more heap */
	if (alloc_cellseg(sc,1))
	{
		x=find_consecutive_cells(sc,n);
		if (x != &g_nil)  return x;
	}

	printf("No Memory ! ! !\n");
	while(true) getchar();
	return &g_nil;
}

/* get new cons cell */
cell_t* mk_pair(scheme *sc, cell_t* a, cell_t* b, int immutable) {
	cell_t* x = mk_cell(sc,a, b);
	typeflag(x) = T_PAIR;
	if(immutable) setimmutable(x);
	car(x) = a;
	cdr(x) = b;
	return (x);
}

//将链表反序
static cell_t* reverse(scheme *sc, cell_t* old_list) {
	cell_t* new_list = &g_nil;
	for ( ; is_pair(old_list); old_list = cdr(old_list)) {
		new_list = cons(sc, car(old_list), new_list);
	}
	return new_list;
}

//list* ,例子 (list* 1 2 3) => (1  2 . 3)
static cell_t* list_star(scheme *sc, cell_t* old_list) {
	old_list=reverse(sc,old_list);
	cell_t* new_list=car(old_list);
	old_list=cdr(old_list);
	while(is_pair(old_list)) {
		new_list=cons(sc,car(old_list),new_list);
		old_list=cdr(old_list);
	}
	return new_list;
}

/* append list -- produce new list (in reverse order) */
//如果acc 为 (4 3) ,  list 为 (5 6) , 则最后返回结果应当为 (6 5 4 3)
static cell_t* revappend(scheme *sc, cell_t* acc, cell_t* list) {
	while (is_pair(list)) {
		acc = cons(sc, car(list), acc);
		list = cdr(list);
	}
	if (list == &g_nil) return acc;
	return &g_false;   /* signal an error */
}

/* Result is:
proper list: length		
circular list: -1			//环行链表
not even a pair: -2	//如果是这样的形式(a . b) （b不是pair）
dotted list: -2 minus length before dot	//pair 链表的最后一个cell不是nil
*/
int list_length(scheme *sc, cell_t* a) {
	int len=0;
	cell_t* slow= a; 
	cell_t* fast= a;
	while (true)
	{
		if (fast == &g_nil) return len;
		if (!is_pair(fast)) return -2 - len;
		fast = cdr(fast);
		++len;
		if (fast == &g_nil) return len;
		if (!is_pair(fast)) return -2 - len;
		fast = cdr(fast);
		++len;
		slow = cdr(slow);
		//如果a中有一个环 fast 和slow都会最终进入这个环中，并且有于fast是slow的速度的两倍，索引fast最终能赶上slow
		if (fast == slow) return -1;
	}
}

static int is_list(scheme *sc, cell_t* a)
{ 
	return list_length(sc,a) >= 0; 
}

/* Round to nearest. Round to even if midway */
//将浮点数四舍五入到整数
static double round_per_r5rs(double x) {
	double fl=floor(x);
	double ce=ceil(x);
	double dfl=x-fl;
	double dce=ce-x;
	if(dfl>dce) {
		return ce;
	} else if(dfl<dce) {
		return fl;
	} else {
		if(fmod(fl,2.0)==0.0) {       /* I imagine this holds */
			return fl;
		} else {
			return ce;
		}
	}
}

/* get number atom (integer) */
cell_t* mk_integer(scheme *sc, long num) {
	cell_t* x = mk_cell(sc,&g_nil, &g_nil);
	typeflag(x) = (T_NUMBER | T_ATOM);
	inital_num(&x->_num,num);
	return (x);
}

cell_t* mk_real(scheme *sc, double num) {
	cell_t* x = mk_cell(sc,&g_nil, &g_nil);
	typeflag(x) = (T_NUMBER | T_ATOM);
	inital_num(&x->_num,num);
	return (x);
}

static cell_t* mk_number(scheme *sc, num_t n) {
	if(n.is_fix) return mk_integer(sc,n.i);
	else return mk_real(sc,n.f);
}

static num_t num_add(num_t a, num_t b) {
	num_t ret;
	ret.is_fix=a.is_fix && b.is_fix;
	if(ret.is_fix) {
		ret.i= a.i+b.i;
	} else {
		ret.f=num2float(a)+num2float(b);
	}
	return ret;
}

static num_t num_sub(num_t a, num_t b) {
	num_t ret;
	ret.is_fix=a.is_fix && b.is_fix;
	if(ret.is_fix) {
		ret.i= a.i-b.i;
	} else {
		ret.f=num2float(a)-num2float(b);
	}
	return ret;
}

static num_t num_mul(num_t a, num_t b) {
	num_t ret;
	ret.is_fix=a.is_fix && b.is_fix;
	if(ret.is_fix) {
		ret.i= a.i*b.i;
	} else {
		ret.f=num2float(a)*num2float(b);
	}
	return ret;
}

static num_t num_div(num_t a, num_t b) {
	num_t ret;
	ret.is_fix=a.is_fix && b.is_fix && a.i%b.i==0;
	if(ret.is_fix) {
		ret.i= a.i/b.i;
	} else {
		ret.f=num2float(a)/num2float(b);
	}
	return ret;
}

static num_t num_intdiv(num_t a, num_t b) {
	num_t ret;
	ret.is_fix=a.is_fix && b.is_fix;
	if(ret.is_fix) {
		ret.i= a.i/b.i;
	} else {
		ret.f=num2float(a)/num2float(b);
	}
	return ret;
}

static num_t num_rem(num_t a, num_t b) {//求余
	long e1=num2int(a);
	long e2=num2int(b);
	long res=e1%e2;
	/* remainder should have same sign as first operand *///余数必须和第一个操作数符号相同
	if ((res > 0) &&(e1 < 0)) res -= labs(e2);
	else if ((res < 0) &&(e1 > 0)) res += labs(e2);
	num_t ret;
	ret.is_fix=a.is_fix && b.is_fix;
	ret.i=res;
	return ret;
}

static num_t num_mod(num_t a, num_t b) {
	long e1=num2int(a);
	long e2=num2int(b);
	long res=e1%e2;
	/* modulo should have same sign as second operand */
	if (res * e2 < 0) {
		res += e2;
	}
	num_t ret;
	ret.is_fix=a.is_fix && b.is_fix;
	ret.i=res;
	return ret;
}

static int num_eq(num_t a, num_t b) {
	int ret;
	int is_fixnum=a.is_fix && b.is_fix;
	if(is_fixnum) {
		ret= a.i==b.i;
	} else {
		ret=num2float(a)==num2float(b);
	}
	return ret;
}

static int num_gt(num_t a, num_t b) {
	int ret;
	int is_fixnum=a.is_fix && b.is_fix;
	if(is_fixnum) {
		ret= a.i>b.i;
	} else {
		ret=num2float(a)>num2float(b);
	}
	return ret;
}

static int num_lt(num_t a, num_t b) {
	int ret;
	int is_fixnum=a.is_fix && b.is_fix;
	if(is_fixnum) {
		ret= a.i<b.i;
	} else {
		ret=num2float(a)<num2float(b);
	}
	return ret;
}

static int num_ge(num_t a, num_t b) {
	return !num_lt(a,b);
}

static int num_le(num_t a, num_t b) {
	return !num_gt(a,b);
}

static int is_zero_double(double x) {//判断一个浮点数是否近似为0
	return x<DBL_MIN && x>-DBL_MIN;
}

static long binary_decode(const char *s) {//将字符串形式的二进制数据转化为整数
	long x=0;
	while(*s!=0 && (*s=='1' || *s=='0')) {
		x<<=1;
		x+=*s-'0';
		s++;
	}
	return x;
}

//数组操作
static void fill_vector(cell_t* vec, cell_t* fill_obj) {
	int num=ivalue(vec)/2+ivalue(vec)%2;
	for(int i=0; i<num; i++) {
		typeflag(vec+1+i) = T_PAIR;
		setimmutable(vec+1+i);//不可变的
		car(vec+1+i)=fill_obj;//填充数组的内容
		cdr(vec+1+i)=fill_obj;//填充数组的内容
	}
}

static cell_t* mk_vector(scheme *sc, int len){ //创建数组
	//一个cell中的 _cons可以保存两个元素，所以只要len/2+len%2个cell就可以保存len个元素
	cell_t* cells = get_consecutive_cells(sc,len/2+len%2+1);// 必能分配成功，失败不会返回
	//cells[0]用于保存数组控制信息
	typeflag(cells) = (T_VECTOR | T_ATOM);//是数组，并是一个原子
	inital_num(&cells->_num,(long)len);//设置数组的长度
	fill_vector(cells,&g_nil);
	return cells;
}

static cell_t* get_vector_item(cell_t* vec, int index) {//取数组中的第index个元素
	int n=index/2;
	if(index%2==0) {
		return car(vec+1+n);
	} else {
		return cdr(vec+1+n);
	}
}

static cell_t* set_vector_item(cell_t* vec, int index, cell_t* a) {//设置数组中的第index个元素的值
	int n=index/2;
	if(index%2==0) {
		return car(vec+1+n)=a;
	} else {
		return cdr(vec+1+n)=a;
	}
}

cell_t* mk_character(scheme *sc, int c) {
	cell_t* x = mk_cell(sc,&g_nil, &g_nil);
	typeflag(x) = (T_CHAR | T_ATOM);
	inital_num(&x->_num,(long)c);
	return (x);
}

/* allocate name to string area */
static char *store_string(scheme *sc, int len, const char *str, char fill) {
	char *buf=(char*)sc->malloc(len+1);
	if(str!=0) {
		_snprintf(buf, len+1, "%s", str);
	} else {
		memset(buf, fill, len);
		buf[len]=0;
	}
	return buf;
}

cell_t* mk_string_n(scheme *sc, const char *str, int len) {
	cell_t* x = mk_cell(sc, &g_nil, &g_nil);
	typeflag(x) = (T_STRING | T_ATOM);
	string_value(x) = store_string(sc,len,str,0);
	string_len(x) = len;
	return (x);
}

cell_t* mk_string(scheme *sc, const char *str) {
	return mk_string_n(sc,str,strlen(str));
}

cell_t* mk_empty_string(scheme *sc, int len, char fill) {
	cell_t* x = mk_cell(sc, &g_nil, &g_nil);
	typeflag(x) = (T_STRING | T_ATOM);
	string_value(x) = store_string(sc,len,0,fill);
	string_len(x) = len;
	return (x);
}

//端口
static int file_interactive(scheme *sc) {
	return sc->top_file_index==0 && 
		sc->load_stack[0].kind&port_file && 
		sc->load_stack[0].f.file==stdin;
}

static cell_t* mk_port(scheme *sc, port_t *p) {
	cell_t* x = mk_cell(sc, &g_nil, &g_nil);
	typeflag(x) = T_PORT|T_ATOM;
	x->_port=p;
	return (x);
}

static void port_close(scheme *sc, cell_t* p, int flag) {
	port_t *pt=p->_port;
	pt->kind&=~flag;
	if((pt->kind & (port_input|port_output))==0) {
		if(pt->kind&port_file) {
			if(pt->f.filename) sc->free(pt->f.filename);
			fclose(pt->f.file);
		}
		pt->kind=port_free;
	}
}

static int push_load_file(scheme *sc, const char *fname) {
	if (sc->top_file_index == MAX_FILES-1) return 0;
	FILE *fin=fopen(fname,"r");
	if(fin!=0) {
		sc->top_file_index++;
		sc->load_stack[sc->top_file_index].kind=port_file|port_input;
		sc->load_stack[sc->top_file_index].f.file=fin;
		sc->load_stack[sc->top_file_index].f.closeit=1;
		sc->load_stack[sc->top_file_index].f.curr_line = 0;
		if(fname) sc->load_stack[sc->top_file_index].f.filename = store_string(sc, strlen(fname), fname, 0);
		sc->nesting_stack[sc->top_file_index]=0;
		sc->loadport->_port=sc->load_stack+sc->top_file_index;
	}
	return fin!=0;
}

static void pop_load_file(scheme *sc) {
	if(sc->top_file_index != 0) {
		sc->nesting=sc->nesting_stack[sc->top_file_index];
		port_close(sc,sc->loadport,port_input);
		sc->top_file_index--;
		sc->loadport->_port=sc->load_stack+sc->top_file_index;
	}
}

static cell_t* port_from_file(scheme *sc, FILE *f, int prop) {
	port_t *pt = (port_t *)sc->malloc(sizeof *pt);
	pt->kind = port_file | prop;
	pt->f.file = f;
	pt->f.closeit = 0;
	return mk_port(sc,pt);
}

static cell_t* port_from_filename(scheme *sc, const char *file_name, int prop) {
	char *mode="r";
	if(prop==(port_input|port_output)) mode="a+";
	else if(prop==port_output) mode="w";
	FILE *f=fopen(file_name,mode);
	if(f==0) return 0;
	port_t *pt = (port_t *)sc->malloc(sizeof *pt);
	pt->kind = port_file | prop;
	pt->f.file = f;
	pt->f.closeit=1;
	pt->f.curr_line = 0;
	if(file_name) pt->f.filename = store_string(sc, strlen(file_name), file_name, 0);
	return mk_port(sc,pt);
}

//为字符串类型的端口重新分配内存
static int realloc_port_string(scheme *sc, port_t *p)
{
	char *data=p->s.start;
	size_t data_size=p->s.end-p->s.start;
	size_t new_size=data_size+BLOCK_SIZE+1;
	p->s.start=(char*)sc->malloc(new_size);
	memset(p->s.start,0,new_size);
	if(data) strcpy(p->s.start,data);
	p->s.end=p->s.start+new_size;
	p->s.curr=p->s.start+data_size;
	if(data) sc->free(data);
	return 1;
}

static cell_t* port_from_string(scheme *sc, char *start, char *end, int prop) {
	port_t *pt=(port_t*)sc->malloc(sizeof(port_t));
	pt->kind=port_string|prop;
	pt->s.start=start;
	pt->s.end=end;
	if(!start)  realloc_port_string(sc,pt);
	pt->s.curr=pt->s.start;
	return mk_port(sc,pt);
}

void write_char(scheme *sc, int c) {
	port_t *pt=sc->outport->_port;
	if(pt->kind&port_file) {
		fputc(c,pt->f.file);
	} else {
		if(pt->s.curr!=pt->s.end) {
			*pt->s.curr++=c;
		} else if(pt->kind&port_can_realloc&&realloc_port_string(sc,pt)) {
			*pt->s.curr++=c;
		}
	}
}

void write_string(scheme *sc, const char *s) {
	port_t *pt=sc->outport->_port;
	int len=strlen(s);
	if(pt->kind&port_file) {
		fwrite(s,1,len,pt->f.file);
	} else {
		for(;len;len--) {
			if(pt->s.curr!=pt->s.end) {
				*pt->s.curr++=*s++;
			} else if(pt->kind&port_can_realloc&&realloc_port_string(sc,pt)) {
				*pt->s.curr++=*s++;
			}
		}
	}
}

/* get new character from input file */
static int get_char(scheme *sc) {
	port_t *pt = sc->inport->_port;
	if(pt->kind & port_eof) return EOF;
	int c = 0;
	if(pt->kind & port_file) {
		c = fgetc(pt->f.file);
	} else {
		if(*pt->s.curr == 0 || pt->s.curr == pt->s.end) {
			c = EOF;
		} else {
			c = *pt->s.curr++;
		}
	}
	if(c == EOF ) pt->kind |= port_eof;
	return c;
}

/* back character to input buffer */
static void unget_char(scheme *sc, int c) {
	if(c==EOF) return;
	port_t *pt=sc->inport->_port;
	if(pt->kind&port_file) {
		ungetc(c,pt->f.file);
	} else {
		if(pt->s.curr!=pt->s.start) pt->s.curr--;
		else false;//error ！！！
	}
}

/* check c is in chars */
static  int find_char_in_string(char *s, int c) {
	if(c==EOF) return 1;
	while (*s){
		if (*s++ == c) return 1;
	}
	return 0;
}

/* skip white characters */
static  int skipspace(scheme *sc) {
	int c = 0, curr_line = 0;
	do {
		c=get_char(sc);
		if(c=='\n') curr_line++;
	} while (isspace(c));
	if (sc->load_stack[sc->top_file_index].kind & port_file)
		sc->load_stack[sc->top_file_index].f.curr_line += curr_line;
	if(c!=EOF) {
		unget_char(sc,c);
		return 1;
	}
	else return EOF;
}

/* read characters up to delimiter, but cater to character constants */
//读取一个字符串直到遇到分隔符
static char *readstr_upto(scheme *sc, char *delim) {
	char *p = sc->strbuff;
	while ((p - sc->strbuff < sizeof(sc->strbuff)) &&
		!find_char_in_string(delim, (*p++ = get_char(sc)))); //读取字符串，直到遇到一个分隔符
	unget_char(sc,p[-1]);
	*--p = '\0';
	return sc->strbuff;
}

/* read string expression "xxx...xxx" */
//将一个字符串字面量转换为字符串
static cell_t* readstrexp(scheme *sc) {
	char *p = sc->strbuff;
	int c1=0;
	enum { st_ok, st_bsl, st_x1, st_x2, st_oct1, st_oct2 } state=st_ok;

	for (;;) {
		int c=get_char(sc);
		if(c == EOF || p-sc->strbuff > sizeof(sc->strbuff)-1) {
			return &g_false;
		}
		switch(state) {
			case st_ok:
				switch(c) {
					case '\\':
						state=st_bsl;
						break;
					case '"':
						*p=0;
						return mk_string_n(sc,sc->strbuff, p - sc->strbuff);
					default:
						*p++=c;
						break;
				}
				break;
			case st_bsl:
				switch(c) {
					case '0':
					case '1':
					case '2':
					case '3':
					case '4':
					case '5':
					case '6':
					case '7':
						state=st_oct1;
						c1=c-'0';
						break;
					case 'x':
					case 'X':
						state=st_x1;
						c1=0;
						break;
					case 'n':
						*p++='\n';
						state=st_ok;
						break;
					case 't':
						*p++='\t';
						state=st_ok;
						break;
					case 'r':
						*p++='\r';
						state=st_ok;
						break;
					case '"':
						*p++='"';
						state=st_ok;
						break;
					default:
						*p++=c;
						state=st_ok;
						break;
				}
				break;
			case st_x1:
			case st_x2:
				c=toupper(c);
				if(c>='0' && c<='F') {
					if(c<='9') {
						c1=(c1<<4)+c-'0';
					} else {
						c1=(c1<<4)+c-'A'+10;
					}
					if(state==st_x1) {
						state=st_x2;
					} else {
						*p++=c1;
						state=st_ok;
					}
				} else {
					return &g_false;
				}
				break;
			case st_oct1:
			case st_oct2:
				if (c < '0' || c > '7')
				{
					*p++=c1;
					unget_char(sc, c);
					state=st_ok;
				}
				else
				{
					if (state==st_oct2 && c1 >= 32)
						return &g_false;

					c1=(c1<<3)+(c-'0');

					if (state == st_oct1)
						state=st_oct2;
					else
					{
						*p++=c1;
						state=st_ok;
					}
				}
				break;
		}
	}
}

/* get token */
static int token(scheme *sc) {
	int c = skipspace(sc);
	if(c == EOF)  return (TOK_EOF); 
	switch (c=get_char(sc)) {
		case EOF:
			return (TOK_EOF);
		case '(':
			return (TOK_LPAREN);
		case ')':
			return (TOK_RPAREN);
		case '.':
			c=get_char(sc);
			if(find_char_in_string(" \n\t",c)) {
				return (TOK_DOT);
			} else {
				unget_char(sc,c);
				unget_char(sc,'.');
				return TOK_ATOM;
			}
		case '\''://引用
			return (TOK_QUOTE);
		case ';'://注释
			while ((c=get_char(sc)) != '\n' && c!=EOF)  ; //跳过注释
			if(c == '\n' && sc->load_stack[sc->top_file_index].kind & port_file)
				sc->load_stack[sc->top_file_index].f.curr_line++;
			if(c == EOF) return TOK_EOF;
			else return token(sc);
		case '"'://双引号
			return (TOK_DQUOTE);
		case '`'://准引用
			return (TOK_BQUOTE);
		case ',':
			if ((c=get_char(sc)) == '@') {
				return (TOK_ATMARK);
			} else {
				unget_char(sc,c);
				return (TOK_COMMA);
			}
		case '#':
			c=get_char(sc);
			if (c == '(') return TOK_VECTOR;
			else if(c == '!') {//#!开头的注释
				while ((c=get_char(sc)) != '\n' && c!=EOF);
				if(c == '\n' && sc->load_stack[sc->top_file_index].kind & port_file)
					sc->load_stack[sc->top_file_index].f.curr_line++;
				if(c == EOF) return TOK_EOF;
				return token(sc);
			} else {
				unget_char(sc,c);
				if(find_char_in_string(" tfodxb\\",c)) return TOK_SHARP_CONST;
				else return (TOK_SHARP);
			}
		default:
			unget_char(sc,c);
			return (TOK_ATOM);
	}
}

#define   ok_abbrev(p)   (is_pair(p) && cdr(p) == &g_nil)
//打印一个字符串为字符串字面量
static void printslashstring(scheme *sc, char *p, int len) {
	unsigned char *s=(unsigned char*)p;
	write_char(sc,'"');
	for (int  i=0; i<len; i++) {
		if(*s==0xff || *s=='"' || *s=='\\' || *s<' ') {
			write_char(sc,'\\');
			switch(*s) {
				case '"':
					write_char(sc,'"');
					break;
				case '\n':
					write_char(sc,'n');
					break;
				case '\t':
					write_char(sc,'t');
					break;
				case '\r':
					write_char(sc,'r');
					break;
				case '\\':
					write_char(sc,'\\');
					break;
				default: {
					int d=*s/16;
					write_char(sc,'x');
					if(d<10) {
						write_char(sc,d+'0');
					} else {
						write_char(sc,d-10+'A');
					}
					d=*s%16;
					if(d<10) {
						write_char(sc,d+'0');
					} else {
						write_char(sc,d-10+'A');
					}
				}
			}
		} else {
			write_char(sc,*s);
		}
		s++;
	}
	write_char(sc,'"');
}

/* Uses internal buffer unless string cell* is already available */
static void atom2str(scheme *sc, cell_t* l, int flag, char **pp, int *plen) {
	char *p= sc->strbuff;
	if (l == &g_nil) {
		p = "()";
	} else if (l == &g_true) {
		p = "#t";
	} else if (l == &g_false) {
		p = "#f";
	} else if (l == &g_eof) {
		p = "#<EOF>";
	} else if (is_port(l)) {
		p = "#<PORT>";
	} else if (is_symbol(l)) {
		p = sym_name(l);
	}  else if (is_macro(l)) {
		p = "#<MACRO>";
	} else if (is_closure(l)) {
		p = "#<CLOSURE>";
	} else if (is_promise(l)) {
		p = "#<PROMISE>";
	}else if (is_proc(l)) {
		_snprintf(p,STR_BUFF_SIZE,"#<%s PROCEDURE %ld>", proc_name(l),proc_value(l));
	} else if (is_foreign(l)) {
		_snprintf(p,STR_BUFF_SIZE,"#<FOREIGN PROCEDURE %ld>", proc_value(l));
	} else if (is_continuation(l)) {
		p = "#<CONTINUATION>";
	}else if (is_number(l)) {
		p = sc->strbuff;
		if (flag <= 1 || flag == 10) /* f is the base for numbers if > 1 */ {
			if(l->_num.is_fix) {
				_snprintf(p, STR_BUFF_SIZE, "%ld", l->_num.i);
			} else {
				_snprintf(p, STR_BUFF_SIZE, "%.10g", l->_num.f);
				/* r5rs says there must be a '.' (unless 'e'?) */
				flag = strcspn(p, ".e");
				if (p[flag] == 0) {
					p[flag] = '.'; /* not found, so add '.0' at the end */
					p[flag+1] = '0';
					p[flag+2] = 0;
				}
			}
		} else {
			long v = ivalue(l);
			if (flag == 16) {
				if (v >= 0)
					_snprintf(p, STR_BUFF_SIZE, "%lx", v);
				else
					_snprintf(p, STR_BUFF_SIZE, "-%lx", -v);
			} else if (flag == 8) {
				if (v >= 0)
					_snprintf(p, STR_BUFF_SIZE, "%lo", v);
				else
					_snprintf(p, STR_BUFF_SIZE, "-%lo", -v);
			} else if (flag == 2) {
				unsigned long b = (v < 0) ? -v : v;
				p = &p[STR_BUFF_SIZE-1];
				*p = 0;
				do { *--p = (b&1) ? '1' : '0'; b >>= 1; } while (b != 0);
				if (v < 0) *--p = '-';
			}
		}
	} else if (is_string(l)) {
		if (!flag) {
			p = string_value(l);
		} else { /* Hack, uses the fact that printing is needed */
			*pp=sc->strbuff;
			*plen=0;
			printslashstring(sc, string_value(l), string_len(l));
			return;
		}
	} else if (is_character(l)) {
		int c=char_value(l);
		if (!flag) {
			p[0]=c;
			p[1]=0;
		} else {
			switch(c) {
				case ' ':
					_snprintf(p,STR_BUFF_SIZE,"#\\space"); break;
				case '\n':
					_snprintf(p,STR_BUFF_SIZE,"#\\newline"); break;
				case '\r':
					_snprintf(p,STR_BUFF_SIZE,"#\\return"); break;
				case '\t':
					_snprintf(p,STR_BUFF_SIZE,"#\\tab"); break;
				default:
					if(c==127) {
						_snprintf(p,STR_BUFF_SIZE, "#\\del");
						break;
					} else if(c<32) {
						_snprintf(p, STR_BUFF_SIZE, "#\\%s", charnames[c]);
						break;
					}
					_snprintf(p,STR_BUFF_SIZE,"#\\%c",c); break;
					break;
				}
		}
	}  else {
		p = "#<ERROR>";
	}
	*pp=p;
	*plen=strlen(p);
}

/* print atoms */
static void printatom(scheme *sc, cell_t* l, int f) {
	char *p;
	int len;
	atom2str(sc,l,f,&p,&len);
	write_string(sc,p);
}

/* make symbol or number atom from string */
static cell_t* mk_atom_from_string(scheme *sc, char *q) {
	char*p=q;
	int has_dec_point=0;
	int has_fp_exp = 0;
	char c = *p++;
	if ((c == '+') || (c == '-')) c = *p++;
	if (c == '.') {
		has_dec_point=1;
		c = *p++;
	} 
	if (!isdigit(c)) {
		return (mk_symbol(sc, strlwr(q)));
	}
	for ( ; (c = *p) != 0; ++p) {
		//判断是不是符合数字格式的标准
		if (!isdigit(c)) {
			if(c=='.') {
				if(!has_dec_point) {
					has_dec_point=1;
					continue;
				}
			}
			else if ((c == 'e') || (c == 'E')) {
				if(!has_fp_exp) {
					has_dec_point = 1; /* decimal point illegal from now on */
					p++;
					if ((*p == '-') || (*p == '+') || isdigit(*p)) {
						continue;
					}
				}
			}
			return (mk_symbol(sc, strlwr(q)));
		}
	}
	if(has_dec_point) {
		return mk_real(sc,atof(q));
	}
	return (mk_integer(sc, atol(q)));
}

//解析 # 字符开头的字符串 用于生成常量（不包括数组）
static cell_t* mk_sharp_const(scheme *sc, char *name) {
	char tmp[STR_BUFF_SIZE];
	long x=0;
	if (!strcmp(name, "t"))
		return (&g_true);
	else if (!strcmp(name, "f"))
		return (&g_false);
	else if (*name == 'o') {/* #o (octal) */
		_snprintf(tmp, STR_BUFF_SIZE, "0%s", name+1);
		sscanf(tmp, "%lo", (long unsigned *)&x);
		return (mk_integer(sc, x));
	} else if (*name == 'd') {    /* #d (decimal) */
		sscanf(name+1, "%ld", (long int *)&x);
		return (mk_integer(sc, x));
	} else if (*name == 'x') {    /* #x (hex) */
		_snprintf(tmp, STR_BUFF_SIZE, "0x%s", name+1);
		sscanf(tmp, "%lx", (long unsigned *)&x);
		return (mk_integer(sc, x));
	} else if (*name == 'b') {    /* #b (binary) */
		x = binary_decode(name+1);
		return (mk_integer(sc, x));
	} else if (*name == '\\') { /* #\w (character) */
		int c=0;
		if(stricmp(name+1,"space")==0) {
			c=' ';
		} else if(stricmp(name+1,"newline")==0) {
			c='\n';
		} else if(stricmp(name+1,"return")==0) {
			c='\r';
		} else if(stricmp(name+1,"tab")==0) {
			c='\t';
		} else if(name[1]=='x' && name[2]!=0) {
			int c1=0;
			if(sscanf(name+2,"%x",(unsigned int *)&c1)==1 && c1 < UCHAR_MAX) {
				c=c1;
			} else {
				return &g_nil;
			}
		} else if(is_ascii_name(name+1,&c)) {

		} else if(name[2]==0) {
			c=name[1];
		} else {
			return &g_nil;
		}
		return mk_character(sc,c);
	} else
		return (&g_nil);
}

/* equivalence of atoms */
int eqv(cell_t* a, cell_t* b) {
	if (is_string(a)) {
		if (is_string(b)) return (string_value(a) == string_value(b));
		else return (0);
	} 
	else if (is_number(a)) {
		if (is_number(b)) {
			if (a->_num.is_fix == b->_num.is_fix)
				return num_eq(nvalue(a),nvalue(b));
		}
		return (0);
	} 
	else if (is_character(a)) {
		if (is_character(b)) return char_value(a)==char_value(b);
		else return (0);
	} 
	else if (is_port(a)) {
		if (is_port(b)) return a==b;
		else return (0);
	} 
	else if (is_proc(a)) {
		if (is_proc(b)) return proc_value(a)==proc_value(b);
		else return (0);
	} 
	else {
		return (a == b);
	}
}

cell_t* mk_foreign_func(scheme *sc, foreign_func_t f) {
	cell_t* x = mk_cell(sc, &g_nil, &g_nil);
	typeflag(x) = (T_FOREIGN | T_ATOM);
	x->_fun=f;
	return (x);
}

/* make closure. c is code. e is environment */ //创建闭包
static cell_t* mk_closure(scheme *sc, cell_t* code, cell_t* env) {
	cell_t* p = mk_cell(sc, code, env);
	typeflag(p) = T_CLOSURE;
	return p;
}

/* make continuation. */ //创建延续
static cell_t* mk_continuation(scheme *sc, cell_t* d) {
	cell_t* p = mk_cell(sc, &g_nil, d);
	typeflag(p) = T_CONTINUATION;
	return p;
}

//符号列表初始化
static cell_t* oblist_initial_value(scheme *sc)
{
	return mk_vector(sc, 461); /* probably should be bigger */
}
// 创建一个新的符号
static cell_t* oblist_add_by_name(scheme *sc, const char *name)
{
	cell_t* sym = immutable_cons(sc, mk_string(sc, name), &g_nil);//符号内部像这样("name1")
	typeflag(sym) = T_SYMBOL;//类型为符号
	setimmutable(car(sym));
	int location = hash_fn(name, ivalue_unchecked(sc->oblist));
	//get_vector_item(sc->oblist, location) 等价于  (vector-ref sc->oblist location)    求值结果是一个符号链表 (symbol ...)
	set_vector_item(sc->oblist, location,immutable_cons(sc, sym, get_vector_item(sc->oblist, location)));//将新的符号加入链表头部
	return sym;
}
//查找一个符号
static  cell_t* oblist_find_by_name(scheme *sc, const char *name)
{
	int location = hash_fn(name, ivalue_unchecked(sc->oblist));
	for (cell_t* sym_list = get_vector_item(sc->oblist, location); sym_list != &g_nil;sym_list = cdr(sym_list)) {
		char *s = sym_name(car(sym_list));
		if(stricmp(name, s) == 0) return car(sym_list);//返回一个符号
	}
	return &g_nil;
}
//返回所有符号的列表
static cell_t* oblist_all_symbols(scheme *sc)
{
	cell_t* ob_list = &g_nil;
	for (int i = 0; i < ivalue_unchecked(sc->oblist); i++) {
		for (cell_t* sym_list  = get_vector_item(sc->oblist, i); sym_list != &g_nil; sym_list = cdr(sym_list)) {
			ob_list = cons(sc, car(sym_list), ob_list);
		}
	}
	return ob_list;//返回符号列表 (smybol ...)
}
//添加一个符号，如果有这个符号，就返回已有的那个
cell_t* mk_symbol(scheme *sc, const char *name) {
	/* first check oblist */
	cell_t* sym = oblist_find_by_name(sc, name);
	if (sym != &g_nil) return sym;
	return  oblist_add_by_name(sc, name);
}
//生成一个名字唯一的符号
cell_t* gensym(scheme *sc) {
	static long s_gensym_cnt=0;
	for(; s_gensym_cnt<LONG_MAX; s_gensym_cnt++) {
		char name[40];
		_snprintf(name,40,"gensym-%ld",s_gensym_cnt);
		cell_t* sym = oblist_find_by_name(sc, name);
		if (sym != &g_nil) continue;
		return  oblist_add_by_name(sc, name);
	}
	return &g_nil;
}

/* ========== Environment  ========== */
//一些数据结构的表示形式
//symbol : (string ,nil)
//symbol_list : (symbol , symbol_list) | nil
//symbol_kv : (smybol , any)
//slot : symbol_kv
//symbol_kv_list : (symbol_kv , symbol_kv_list) |  nil
//environment : ( symbol_kv_list,environment) | ( vector<symbol_kv_list>)
// closure : ( (symbol_list code) env)

static void new_frame_in_env(scheme *sc, cell_t* old_env)
{
	cell_t* new_frame= &g_nil;
	if (old_env == &g_nil) new_frame = mk_vector(sc, 461);
	sc->envir = immutable_cons(sc, new_frame, old_env);
	typeflag(sc->envir) = T_ENVIRONMENT;
}

static void new_slot_in_env(scheme *sc, cell_t* env,cell_t* sym,cell_t* value)
{
	cell_t* slot/*symbol_kv*/= immutable_cons(sc, sym, value);
	if (is_vector(car(env))) {
		int location = hash_fn(sym_name(sym), ivalue_unchecked(car(env)));
		set_vector_item(car(env), location, immutable_cons(sc, slot, get_vector_item(car(env), location)));
	} else {
		car(env) = immutable_cons(sc, slot, car(env));
	}
}

static void new_slot_in_env(scheme *sc, cell_t* sym, cell_t* value)
{
	new_slot_in_env(sc, sc->envir, sym, value);
}

static cell_t* find_slot_in_env(scheme *sc, cell_t* env, cell_t* sym, int all)
{
	for (; env != &g_nil; env = cdr(env)) {
		cell_t* item /*symbol_kv_list*/=NULL;
		if (is_vector(car(env))) {
			int location = hash_fn(sym_name(sym), ivalue_unchecked(car(env)));
			item = get_vector_item(car(env), location);
		} else {
			item = car(env);
		}
		for (;item != &g_nil; item = cdr(item)) {
			if (caar(item) == sym) return car(item);
		}
		if(!all) return &g_nil;
	}
	return &g_nil;
}

static  void set_slot_in_env(scheme *sc, cell_t* symbol_kv, cell_t* value)
{
	cdr(symbol_kv) = value;
}

static  cell_t* slot_value_in_env(cell_t* symbol_kv)
{
	return cdr(symbol_kv);
}

void scheme_define(scheme *sc, cell_t* envir, cell_t* symbol, cell_t* value) {
	cell_t* p=find_slot_in_env(sc,envir,symbol,0);
	if (p != &g_nil) set_slot_in_env(sc, p, value);
	else new_slot_in_env(sc, envir, symbol, value);
}

static cell_t* error_helper(scheme *sc, const char * error_desc, cell_t* arg) {
	char buf[STR_BUFF_SIZE];
	port_t& load_pt=sc->load_stack[sc->top_file_index];
	if (load_pt.kind & port_file && load_pt.f.file != stdin) {//如果是一个文件类型的端口 并且不是控制台输入
		_snprintf(buf, STR_BUFF_SIZE, "(%s : %i) %s", 
			load_pt.f.filename?load_pt.f.filename:"<unkown file>", load_pt.f.curr_line+1, error_desc);
		error_desc = (const char*)buf;
	}
	cell_t* symbol_kv=find_slot_in_env(sc,sc->envir,sc->sym_error_hook,1);//查找释放有处理错误的钩子函数
	if (symbol_kv != &g_nil) {//如果找到了钩子函数，由钩子函数来处理这个错误
		if(arg!=0) {
			sc->code = cons(sc, cons(sc, sc->sym_quote, cons(sc,arg, &g_nil)), &g_nil); //结果（用lisp表示）类似这样：(sc->sym_quote arg)
		} else {
			sc->code = &g_nil;
		}
		sc->code = cons(sc, mk_string(sc, error_desc), sc->code);  //结果（用lisp表示）类似这样：(error_desc sc->sym_quote arg)
		setimmutable(car(sc->code));
		sc->code = cons(sc, slot_value_in_env(symbol_kv), sc->code);  //结果（用lisp表示）类似这样：(slot_value_in_env(symbol_kv)  error_desc sc->sym_quote arg)
		sc->op = (int)OP_EVAL;
		return &g_true;
	}
	else{
		if(arg!=0) {
			sc->args = cons(sc, arg, &g_nil);
		} else {
			sc->args = &g_nil;
		}
		sc->args = cons(sc, mk_string(sc, error_desc), sc->args);//结果（用lisp表示）类似这样：(error_desc arg)
		setimmutable(car(sc->args));
		sc->op = (int)OP_ERR0;
		return &g_true;
	}
}
#define Error0(sc,error_desc) return error_helper(sc,error_desc,0)
#define Error1(sc,error_desc, arg) return error_helper(sc,error_desc,arg)

static cell_t* s_return_helper(scheme *sc, cell_t* ret_value) {
	sc->ret_value = ret_value;
	if(sc->call_stack==&g_nil) return &g_nil;
	sc->op = ivalue(car(sc->call_stack));
	sc->args = cadr(sc->call_stack);
	sc->envir = caddr(sc->call_stack);
	sc->code = cadddr(sc->call_stack);
	sc->call_stack = cddddr(sc->call_stack);
	return &g_true;
}
#define s_return(sc,ret_value) return s_return_helper(sc,ret_value)
#define s_retbool(istrue)    s_return(sc,(istrue) ? &g_true : &g_false)
#define s_goto(sc,_op) {sc->op = (int)(_op); return &g_true;}

static void s_save(scheme *sc, opcode op, cell_t* args, cell_t* code) {
	sc->call_stack = cons(sc, code, sc->call_stack);
	sc->call_stack = cons(sc, sc->envir, sc->call_stack);
	sc->call_stack = cons(sc, args, sc->call_stack);
	sc->call_stack = cons(sc, mk_integer(sc, (long)op), sc->call_stack);
}

/* garbage collector  //标记-清除算法
*  We use algorithm E (Knuth, The Art of Computer Programming Vol.1, sec. 2.3.5), 
*  the Schorr-Deutsch-Waite link-inversion algorithm, for marking.
*/
static void mark(cell_t* a) {
	cell_t* t = (cell_t*) 0;
	cell_t* p = a;
E2:  
	setmark(p);
	if(is_vector(p)) {
		int i;
		int num=ivalue_unchecked(p)/2+ivalue_unchecked(p)%2;
		for(i=0; i<num; i++) {
			/* Vector cells will be treated like ordinary cells */
			mark(p+1+i);
		}
	}
	if (is_atom(p))
		goto E6;
	/* E4: down car */
	cell_t* q = car(p);
	if (q && !is_mark(q)) {
		setatom(p);  /* a note that we have moved car */
		car(p) = t;
		t = p;
		p = q;
		goto E2;
	}
E5:  
	q = cdr(p); /* down cdr */
	if (q && !is_mark(q)) {
		cdr(p) = t;
		t = p;
		p = q;
		goto E2;
	}
E6:   /* up.  Undo the link switching from steps E4 and E5. */
	if (!t) return;
	q = t;
	if (is_atom(q)) {
		clratom(q);
		t = car(q);
		car(q) = p;
		p = q;
		goto E5;
	} else {
		t = cdr(q);
		cdr(q) = p;
		p = q;
		goto E6;
	}
}

static void finalize_cell(scheme *sc, cell_t* a) {
	if(is_string(a)) {
		sc->free(string_value(a));
	} else if(is_port(a)) {
		if(a->_port->kind&port_file
			&& a->_port->f.closeit) {
				port_close(sc,a,port_input|port_output);
		}
		sc->free(a->_port);
	}
}

/* garbage collection. parameter a, b is marked. */
static void gc(scheme *sc, cell_t* a, cell_t* b) {
	bool b_out=sc->gc_verbose&&(sc->outport!=&g_nil);
	if(b_out) write_string(sc, "gc start ...");

	/* mark system globals */
	mark(sc->oblist);
	mark(sc->global_env);

	/* mark current registers */
	mark(sc->args);
	mark(sc->envir);
	mark(sc->code);
	mark(sc->call_stack);
	mark(sc->ret_value);
	mark(sc->outport);
	mark(sc->inport);
	mark(sc->save_inport);
	mark(sc->loadport);

	/* mark variables a, b */
	mark(a);
	mark(b);

	/* garbage collect */
	clrmark(&g_nil);
	sc->free_cell_count = 0;
	sc->free_cell = &g_nil;
	/* free-list is kept sorted by address so as to maintain consecutive
	ranges, if possible, for use with vectors. Here we scan the cells
	(which are also kept sorted by address) downwards to build the
	free-list in sorted order.
	*/
	for (int i = sc->last_cell_seg; i >= 0; i--) {
		cell_t* p = sc->cell_seg[i] + CELL_SEGSIZE;
		while (--p >= sc->cell_seg[i]) {
			if (is_mark(p)) {//如果已经标记清除标记位
				clrmark(p);
			} else {//如果未标记，释放该节点
				/* reclaim cell */
				if (typeflag(p) != 0) {
					finalize_cell(sc, p);
					typeflag(p) = 0;
					car(p) = &g_nil;
				}
				++sc->free_cell_count;
				cdr(p) = sc->free_cell;
				sc->free_cell = p;
			}
		}
	}

	if(b_out)  {
		char msg[80];
		_snprintf(msg,80,"done: %ld cells were recovered.\n", sc->free_cell_count);
		write_string(sc,msg);
	}
}

static cell_t* opexe_0(scheme *sc, opcode op) {
	cell_t* x, *y;
	switch (op) {
		case OP_LOAD:       /* load */
			if(file_interactive(sc)) {
				fprintf(sc->outport->_port->f.file,"Loading %s\n", string_value(car(sc->args)));
			}
			if (!push_load_file(sc,string_value(car(sc->args)))) {
				Error1(sc,"unable to open", car(sc->args));
			}
			else{
				sc->args = mk_integer(sc,sc->top_file_index);
				s_goto(sc,OP_T0LVL);
			}
		case OP_T0LVL: /* top level */
			/* If we reached the end of file, this loop is done. */
			if(sc->loadport->_port->kind & port_eof){//如果代码已经被读取完了
				if(sc->top_file_index == 0){//如果是顶层文件读完了，退出解释器
					sc->args=&g_nil;
					s_goto(sc,OP_QUIT);
				}
				else{//如果不是顶层文件，退出该文件
					pop_load_file(sc);
					s_return(sc,sc->ret_value);
				}
			}
			/* If interactive, be nice to user. */
			if(file_interactive(sc)){
				sc->envir = sc->global_env;
				sc->call_stack = &g_nil;
				write_string(sc,"\nts>");
			}
			/* Set up another iteration of REPL */
			sc->nesting=0;
			sc->save_inport=sc->inport;
			sc->inport = sc->loadport;
			s_save(sc,OP_T0LVL, &g_nil, &g_nil);//进入下一个求值循环
			s_save(sc,OP_VALUEPRINT, &g_nil, &g_nil);//打印执行结果
			s_save(sc,OP_EVAL_INTERNAL, &g_nil, &g_nil);//执行
			s_goto(sc,OP_READ_INTERNAL);//编译

		case OP_READ_INTERNAL:       /* internal read */ //编译 读取s表达式
			sc->tok = token(sc);
			if(sc->tok==TOK_EOF) s_return(sc,sc->ret_value); //到这里，表示端口中的代码被读完了，应当返回nil
			s_goto(sc,OP_RDSEXPR);

		case OP_EVAL_INTERNAL: /* top level */ //执行
			sc->code = sc->ret_value;
			sc->inport=sc->save_inport;
			s_goto(sc,OP_EVAL);

		case OP_EVAL:       /* main part of evaluation *///执行
			if (is_symbol(sc->code)) {    /* symbol */ //符号求值为他绑定的值
				x=find_slot_in_env(sc,sc->envir,sc->code,1);
				if (x != &g_nil) {
					s_return(sc,slot_value_in_env(x));
				} else {
					Error1(sc,"eval: unbound variable:", sc->code);
				}
			} else if (is_pair(sc->code)) {//链表求值
				if (is_syntax(x = car(sc->code))) {     /* SYNTAX */ //lambda macro if等开头的链表会通过这个分支处理
					sc->code = cdr(sc->code);
					s_goto(sc,syntax_sym2opcode(x));
				} else {/* first, eval top element and eval arguments */
					s_save(sc,OP_E0ARGS, &g_nil, sc->code);
					/* If no macros => s_save(sc,OP_E1ARGS, sc->NIL, cdr(sc->code));*/
					sc->code = car(sc->code);
					s_goto(sc,OP_EVAL);//计算第一个字段，结果是函数 或者宏
				}
			} else {//其他类型求值结果就是自身
				s_return(sc,sc->code);
			}
		case OP_E0ARGS:     /* eval arguments */
			//sc->code的形式 (first_expr arg ...) 这里first_expr的求值结果可能是宏也可能是闭包
			if (is_macro(sc->ret_value)) {    /* macro expansion */
				//如果结果是一个宏，那么参数不要进一步的处理，而是交给这个宏去处理
				s_save(sc,OP_DOMACRO, &g_nil, &g_nil);//由这个去执行宏生成的代码
				sc->args = cons(sc,sc->code, &g_nil);//sc->args 的形式是 (first_expr arg ...)  注意first_expr也保留了
				sc->code = sc->ret_value;
				s_goto(sc,OP_APPLY);//这里把参数交给宏去处理
			} else {
				sc->code = cdr(sc->code);//(arg ...) 
				s_goto(sc,OP_E1ARGS);
			}
		case OP_E1ARGS:     /* eval arguments */
			sc->args = cons(sc, sc->ret_value, sc->args);
			if (is_pair(sc->code)) { /* continue */ //对每个实参求值
				s_save(sc,OP_E1ARGS, sc->args, cdr(sc->code));
				sc->code = car(sc->code);
				sc->args = &g_nil;
				s_goto(sc,OP_EVAL);
			} else {  /* end */// 实参的值求完了 ，用这些实参调用函数
				sc->args = reverse(sc,sc->args);
				sc->code = car(sc->args);
				sc->args = cdr(sc->args);
				s_goto(sc,OP_APPLY);
			}

		case OP_APPLY:      /* apply 'code' to 'args' */
			if (is_proc(sc->code)) {/* PROCEDURE */
				s_goto(sc,proc_value(sc->code));   
			} else if (is_foreign(sc->code)){
				/* Keep nested calls from GC'ing the arglist */
				//sc->code的形式foreign_proc 
				x=sc->code->_fun(sc,sc->args);
				s_return(sc,x);
			} else if (is_closure(sc->code) || is_macro(sc->code) || is_promise(sc->code)) { /* CLOSURE */
				/* Should not accept promise */
				//sc->code的形式1 (var_name body ...) 
				//sc->code的形式2 ( (var_name ...) body ...) 
				//sc->code的形式3 ( (var_name ...   . var_name) body ...) 
				new_frame_in_env(sc, closure_env(sc->code));//局部变量环境
				x = car(closure_code(sc->code));
				for (y = sc->args;  is_pair(x);   x = cdr(x), y = cdr(y)) {//sc->code的形式2 3
					if (y == &g_nil) Error0(sc,"not enough arguments");
					else new_slot_in_env(sc, car(x), car(y));//绑定函数形参
				}
				if (is_symbol(x)) new_slot_in_env(sc, x, y);//sc->code的形式1 3
				else if(x!=&g_nil) Error1(sc,"syntax error in closure: not a symbol:", x);
				sc->code = cdr(closure_code(sc->code));
				sc->args = &g_nil;
				s_goto(sc,OP_BEGIN);
			} else if (is_continuation(sc->code)) { /* CONTINUATION */
				sc->call_stack = cdr(sc->code);
				s_return(sc,sc->args != &g_nil ? car(sc->args) : &g_nil);
			} else {
				Error0(sc,"illegal function");
			}

		case OP_DOMACRO:    /* do macro */
			sc->code = sc->ret_value;
			s_goto(sc,OP_EVAL);
		case OP_QUOTE:      /* quote */
			s_return(sc,car(sc->code));

		case OP_LAMBDA:     /* lambda */{
			//形式1 (lambda (var_name ...) body ...) 
			//形式2 (lambda var_name expr ...)  例如 
			//这里在init.scm中设置了一个hook用于进行宏展开
			cell_t* hook=find_slot_in_env(sc,sc->envir,sc->sym_compile_hook,1);
			if(hook==&g_nil) {
				//这里sc->code为 ((var_name ...) body ...) 或者(var_name expr ...) 
				s_return(sc,mk_closure(sc, sc->code, sc->envir));
			} else {
				s_save(sc,OP_LAMBDA1,sc->args,sc->code);
				sc->args=cons(sc,sc->code,&g_nil);// 构造参数列表
				sc->code=slot_value_in_env(hook);
				s_goto(sc,OP_APPLY);
			}
		}
		case OP_LAMBDA1:
			s_return(sc,mk_closure(sc, sc->ret_value, sc->envir));//定义闭包
		case OP_MKCLOSURE: /* make-closure */ 
			//形式1 (make-clourse '(lambda? var-name body ...) envir?)      lambda 和 envir是可有可无的
			//形式2 (make-clourse '(lambda? (var-name ...) body ...) envir?)      lambda 和 envir是可有可无的
			//例子 (define f (make-closure '(plus ((car plus) 3 4))))  结果为7
			x=car(sc->args);
			if(car(x)==sc->sym_lambda) x=cdr(x);
			if(cdr(sc->args)==&g_nil) y=sc->envir;
			else y=cadr(sc->args);
			s_return(sc,mk_closure(sc, x, y));

		case OP_DEF0:  /* define */
			//(define var_name expr)
			if(is_immutable(car(sc->code)))
				Error1(sc,"define: unable to alter immutable", car(sc->code));
			if (is_pair(car(sc->code))) {
				//形式1 (define (var_name arg ...) body)
				//例子 (define (fname arg1 arg2) (+arg1 arg2))可以通过这个分支 ，最后结果是闭包 ,这个被变换为 (define fname (lambda (arg1 arg2) (+ arg1 arg2))
				//形式2 (define (var_name . arg) body) //x为(var_name arg ...)  被变换为 (define fname (lambda arg body)
				x = caar(sc->code);
				sc->code = cons(sc, sc->sym_lambda, cons(sc, cdar(sc->code), cdr(sc->code)));
			} else {
				x = car(sc->code);//x为var_name
				sc->code = cadr(sc->code);//sc->code为expr
			}
			if (!is_symbol(x)) Error0(sc,"variable is not a symbol");
			s_save(sc,OP_DEF1, &g_nil, x);
			s_goto(sc,OP_EVAL);
		case OP_DEF1:  /* define */
			//sc->code为var_name
			x=find_slot_in_env(sc,sc->envir,sc->code,0);//在当前环境中查找这个符号，并不是在全局环境中查找，而且不递归查找
			if (x != &g_nil) {
				set_slot_in_env(sc, x, sc->ret_value);
			} else {
				new_slot_in_env(sc, sc->code, sc->ret_value);
			}
			s_return(sc,sc->code);//返回变量名
		case OP_DEFP:  /* defined? */
			//形式 (define? var_name evnir)
			if(cdr(sc->args)!=&g_nil) x=cadr(sc->args);
			else x=sc->envir;
			s_retbool(find_slot_in_env(sc,x,car(sc->args),1)!=&g_nil);

		case OP_SET0:       /* set! */
			//形式 (set! var_name expr)
			if(is_immutable(car(sc->code))) Error1(sc,"set!: unable to alter immutable variable",car(sc->code));
			s_save(sc,OP_SET1, &g_nil, car(sc->code));
			sc->code = cadr(sc->code);//sc->code结果为expr
			s_goto(sc,OP_EVAL);//对expr进行求值
		case OP_SET1:       /* set! */
			//sc->code为 var_name
			y=find_slot_in_env(sc,sc->envir,sc->code,1);
			if (y != &g_nil) {
				set_slot_in_env(sc, y, sc->ret_value);
				s_return(sc,sc->ret_value);
			} else {
				Error1(sc,"set!: unbound variable:", sc->code);
			}

		case OP_BEGIN:      /* begin */
			//形式 (begin body ...) 
			if (!is_pair(sc->code)) s_return(sc,sc->code);//?? 这里这样的代码可以通过(begin . 1)
			if (cdr(sc->code) != &g_nil) {
				s_save(sc,OP_BEGIN, &g_nil, cdr(sc->code));//保存剩余的未求值的部分
			}
			sc->code = car(sc->code);
			s_goto(sc,OP_EVAL);

		case OP_IF0:        /* if */
			//if的形式 (if condition true_body false_body?) ， false_body可有可无
			s_save(sc,OP_IF1, &g_nil, cdr(sc->code));//这里cdr(sc->code) 结果是(true_body false_body?)
			sc->code = car(sc->code);//最后 sc->code 是条件
			s_goto(sc,OP_EVAL);//对条件求值
		case OP_IF1:        /* if */
			if (is_true(sc->ret_value)) sc->code = car(sc->code);//最后sc->code为true_body
			else sc->code = cadr(sc->code);  /* (if #f 1) ==> () because * car(sc->NIL) = sc->NIL *///最后sc->code为false_body
			s_goto(sc,OP_EVAL);//对true_body或者false_body求值

		case OP_LET0:       /* let */ 
			//let的形式 (let let_name? ((var_name init_expr) ...) body_expr ...) 。let_name字段可有可无
			sc->args = &g_nil;
			sc->ret_value = sc->code;//sc->ret_value形式 (let_name? ((var_name init_expr) ...) body_expr ...) 
			//let分为命名的let 和未命名的let
			sc->code = is_symbol(car(sc->code)) ? cadr(sc->code) : car(sc->code);//sc->code形式 ((var_name init_expr) ...)
			s_goto(sc,OP_LET1);
		case OP_LET1:       /* let (calculate parameters) */  //计算每个参数的值
			sc->args = cons(sc, sc->ret_value, sc->args);//这里的结果为 (init_result ...  (let_name? ((var_name init_expr) ...) body_expr ...) )
			if (is_pair(sc->code)) { /* continue */
				if (!is_pair(car(sc->code)) || !is_pair(cdar(sc->code))) {
					Error1(sc, "Bad syntax of binding spec in let :",car(sc->code));
				}
				s_save(sc,OP_LET1, sc->args, cdr(sc->code));
				sc->code = cadar(sc->code);//sc->code形式 init_expr
				sc->args = &g_nil;
				s_goto(sc,OP_EVAL);//对init_expr求值 ，假设其返回值为 init_result
			} else {  /* end */
				sc->args = reverse(sc, sc->args);//反序 结果为  ( (let_name? ((var_name init_expr) ...) body_expr ...) init_result ... )
				sc->code = car(sc->args);//结果为(let_name? ((var_name init_expr) ...) body_expr ...)
				sc->args = cdr(sc->args);//结果为(init_result ... )
				s_goto(sc,OP_LET2);
			}
		case OP_LET2:       /* let */
			new_frame_in_env(sc, sc->envir);//为let创建一个新的环境
			x = is_symbol(car(sc->code)) ? cadr(sc->code) : car(sc->code);//如果第一个节点就是符号，这个符号是let_name，要跳过 ，最后x的结果为((var_name init_expr) ...)
			for ( y = sc->args; y != &g_nil; x = cdr(x), y = cdr(y)) {//y为(init_result ...)
					new_slot_in_env(sc, caar(x), car(y));//caar(x)为var_name , y为 init_result
			}
			if (is_symbol(car(sc->code))) {    /* named let */ //命名let 
				//这里将命名let转化为一个闭包，这里没有尾递归优化
				for (x = cadr(sc->code), sc->args = &g_nil; x != &g_nil; x = cdr(x)) {//x为((var_name init_expr) ...)
					//这个循环的目的就是吧var_name都抽取出来
					if (!is_pair(x))
						Error1(sc, "Bad syntax of binding in let :", x);
					if (!is_list(sc, car(x)))
						Error1(sc, "Bad syntax of binding in let :", car(x));
					sc->args = cons(sc, caar(x), sc->args);//sc->args为(var_name ...) ,这里var_name的顺序和sc->code中对应的var_name的顺序是相反的
				}
				x = mk_closure(sc, cons(sc, reverse(sc, sc->args), cddr(sc->code)), sc->envir);//创建闭包
				new_slot_in_env(sc, car(sc->code), x);//为新创建的闭包定义一个名字
				sc->code = cddr(sc->code);//跳过let_name和var_name初始化部分 ，最后 sc->code 是 ( body_expr ...)
				sc->args = &g_nil;
			} else {
				sc->code = cdr(sc->code);//跳过var_name初始化部分 ，最后 sc->code 是 ( body_expr ...)
				sc->args = &g_nil;
			}
			s_goto(sc,OP_BEGIN);//对( body_expr ...)部分进行求值

		case OP_LETSTAR0:    /* let* */
			//let*的形式是这样的 (let* ((var_name init_expr) ...) body_expr ...)
			if (car(sc->code) == &g_nil) {
				new_frame_in_env(sc, sc->envir);
				sc->code = cdr(sc->code);
				s_goto(sc,OP_BEGIN);
			}
			if(!is_pair(car(sc->code)) || !is_pair(caar(sc->code)) || !is_pair(cdaar(sc->code))) {
				Error1(sc,"Bad syntax of binding spec in let* :",car(sc->code));
			}
			s_save(sc,OP_LETSTAR1, cdr(sc->code), car(sc->code));// cdr(sc->code)为 (body_expr ...)  。 car(sc->code)为 ((var_name init_expr) ...)
			sc->code = cadaar(sc->code);//sc->code最后为init_expr 这个代码要使用let*外层的环境（特别的一个情形是，如果这是个lambda表达式，就会绑定到外层的环境上）
			s_goto(sc,OP_EVAL);//对第一个var_name的初始化表达式求值 ，求值的结果假设为init_result
		case OP_LETSTAR1:    /* let* (calculate parameters) */
			new_frame_in_env(sc, sc->envir);//为let*创建一个环境
			s_goto(sc,OP_LETSTAR2);
		case OP_LETSTAR2:    /* let* (calculate parameters) */
			// sc->args为 (body_expr ...)  。 sc->code为 ((var_name init_expr) ...)
			new_slot_in_env(sc, caar(sc->code), sc->ret_value);// caar(sc->code)为var_name  sc->ret_value为init_result
			sc->code = cdr(sc->code);
			if (is_pair(sc->code)) { /* continue */
				s_save(sc,OP_LETSTAR2, sc->args, sc->code);
				sc->code = cadar(sc->code);//sc->code最后为init_expr
				sc->args = &g_nil;
				s_goto(sc,OP_EVAL); //对init_expr求值
			} else {  /* end */
				sc->code = sc->args;//sc->code最后为(body_expr ...)
				sc->args = &g_nil;
				s_goto(sc,OP_BEGIN);//对(body_expr ...)求值
			}

		case OP_VALUEPRINT: /* print evaluation result */
			if(file_interactive(sc)) {//如果在最高层求值环境中，则打印结果
				sc->print_flag = 1;
				sc->args = sc->ret_value;
				s_goto(sc,OP_P0LIST);
			} else {
				s_return(sc,sc->ret_value); //否则作为load的结果返回
			}
		case OP_GENSYM:
			s_return(sc, gensym(sc));
		default:
			_snprintf(sc->strbuff,STR_BUFF_SIZE,"%d: illegal operator", sc->op);
			Error0(sc,sc->strbuff);
	}
	return &g_true;
}

static cell_t* opexe_1(scheme *sc, opcode op) {
	cell_t* x, *y;
	switch (op) {
		case OP_LET0REC:    /* letrec */  //letrec和let很像
			//形式 (letrec ((var_name init_expr) ... ) body)
			new_frame_in_env(sc, sc->envir);
			sc->args = &g_nil;
			sc->ret_value = sc->code;
			sc->code = car(sc->code);
			s_goto(sc,OP_LET1REC);
		case OP_LET1REC:    /* letrec (calculate parameters) */
			sc->args = cons(sc, sc->ret_value, sc->args);
			if (is_pair(sc->code)) { /* continue */
				if (!is_pair(car(sc->code)) || !is_pair(cdar(sc->code))) {
					Error1(sc, "Bad syntax of binding spec in letrec :",car(sc->code));
				}
				s_save(sc,OP_LET1REC, sc->args, cdr(sc->code));
				sc->code = cadar(sc->code);
				sc->args = &g_nil;
				s_goto(sc,OP_EVAL);
			} else {  /* end */
				sc->args = reverse(sc, sc->args);
				sc->code = car(sc->args);
				sc->args = cdr(sc->args);
				s_goto(sc,OP_LET2REC);
			}
		case OP_LET2REC:    /* letrec */
			for (x = car(sc->code), y = sc->args; y != &g_nil; x = cdr(x), y = cdr(y)) {
				new_slot_in_env(sc, caar(x), car(y));
			}
			sc->code = cdr(sc->code);
			sc->args = &g_nil;
			s_goto(sc,OP_BEGIN);

		case OP_COND0:      /* cond */
			//形式1 (cond (cond_expr ) ...)
			//形式2 (cond (cond_expr  body) ...)
			//形式3 (cond (cond_expr => body) ...)
			if (!is_pair(sc->code)) Error0(sc,"syntax error in cond");
			s_save(sc,OP_COND1, &g_nil, sc->code);
			sc->code = caar(sc->code);//sc->code 变为 cond_expr
			s_goto(sc,OP_EVAL);
		case OP_COND1:      /* cond */
			if (is_true(sc->ret_value)) {
				if ((sc->code = cdar(sc->code)) == &g_nil) s_return(sc,sc->ret_value);//形式1   这里 sc->code 被改变了
				if(car(sc->code)==sc->sym_feed_to) {//形式3 这里如果通过 sc->code 应当为  (=> body)
					if(!is_pair(cdr(sc->code))) Error0(sc,"syntax error in cond");
					//x 为  '(sc->ret_value)  之所以这个样子 
					//1 参数要放到列表里面，2 这里body是一个处理过程，这个形式确保sc->ret_value不被进一步求值直接交给body
					//例子 (cond ('(1 2) => list))   结果 ((1 2))
					x=cons(sc, sc->sym_quote, cons(sc, sc->ret_value, &g_nil));
					sc->code=cons(sc,cadr(sc->code),cons(sc,x,&g_nil));
					s_goto(sc,OP_EVAL);
				}
				s_goto(sc,OP_BEGIN);//形式2  如果到这里 sc->code 应当为  (body)
			} else {//循环求值
				if ((sc->code = cdr(sc->code)) == &g_nil) {
					s_return(sc,&g_nil);
				} else {
					s_save(sc,OP_COND1, &g_nil, sc->code);
					sc->code = caar(sc->code);
					s_goto(sc,OP_EVAL);
				}
			}

		case OP_CASE0:      /* case */
			//形式 (case cond_expr (test_expr body) ...)
			s_save(sc,OP_CASE1, &g_nil, cdr(sc->code));
			sc->code = car(sc->code);//cond_expr
			s_goto(sc,OP_EVAL);//对条件进行求值
		case OP_CASE1:      /* case */
			//sc->code为((test_expr body) ...)
			for (x = sc->code; x != &g_nil; x = cdr(x)) {
				if (!is_pair(y = caar(x))) {
					if (eqv(y, sc->ret_value)) break;
				}
				for ( ; y != &g_nil; y = cdr(y)) {
					if (eqv(car(y), sc->ret_value)) break;
				}
				if (y != &g_nil) break;
			}
			if (x != &g_nil) {
				sc->code = cdar(x);//sc->code 变为 (body)
				s_goto(sc,OP_BEGIN);
			}
			s_return(sc,&g_nil);

		case OP_AND0:       /* and */
			if (sc->code == &g_nil) s_return(sc,&g_true);
			s_save(sc,OP_AND1, &g_nil, cdr(sc->code));
			sc->code = car(sc->code);
			s_goto(sc,OP_EVAL);
		case OP_AND1:       /* and */
			if (is_false(sc->ret_value)) s_return(sc,sc->ret_value);
			else if (sc->code == &g_nil) s_return(sc,sc->ret_value);
			else {
				s_save(sc,OP_AND1, &g_nil, cdr(sc->code));
				sc->code = car(sc->code);
				s_goto(sc,OP_EVAL);
			}

		case OP_OR0:        /* or */
			if (sc->code == &g_nil) s_return(sc,&g_false);
			s_save(sc,OP_OR1, &g_nil, cdr(sc->code));
			sc->code = car(sc->code);
			s_goto(sc,OP_EVAL);
		case OP_OR1:        /* or */
			if (is_true(sc->ret_value)) s_return(sc,sc->ret_value);
			else if (sc->code == &g_nil) s_return(sc,sc->ret_value);
			else {
				s_save(sc,OP_OR1, &g_nil, cdr(sc->code));
				sc->code = car(sc->code);
				s_goto(sc,OP_EVAL);
			}

		case OP_C0STREAM:   /* cons-stream */
			//(cons-stream expr-arg expr-code) 
			//例子 (cons-stream 1 1)   => (1 . #<PROMISE>)
			s_save(sc,OP_C1STREAM, &g_nil, cdr(sc->code));
			sc->code = car(sc->code);
			s_goto(sc,OP_EVAL);
		case OP_C1STREAM:   /* cons-stream */
			sc->args = sc->ret_value;  /* save sc->value to register sc->args for gc */
			x = mk_closure(sc, cons(sc, &g_nil, sc->code), sc->envir);
			typeflag(x)=T_PROMISE;
			s_return(sc,cons(sc, sc->args, x));

		case OP_MACRO0:     /* macro */
			//形式1 (macro (macro-name var-name ...) body ...)
			//形式2 (macro macro-name (lambda ....))
			if (is_pair(car(sc->code))) {//处理形式1
				x = caar(sc->code);//macro-name
				sc->code = cons(sc, sc->sym_lambda, cons(sc, cdar(sc->code), cdr(sc->code)));//lambda表达式 （宏代码）
			} else {//处理形式2
				x = car(sc->code);//macro-name
				sc->code = cadr(sc->code);//lambda表达式 （宏代码）
			}
			if (!is_symbol(x)) Error0(sc,"variable is not a symbol");
			s_save(sc,OP_MACRO1, &g_nil, x);
			s_goto(sc,OP_EVAL);//为这个宏生成一个闭包
		case OP_MACRO1:     /* macro */
			typeflag(sc->ret_value) = T_MACRO;//sc->ret_value是一个闭包，这里吧类型改为宏
			x = find_slot_in_env(sc, sc->envir, sc->code, 0);
			if (x != &g_nil) set_slot_in_env(sc, x, sc->ret_value);//将宏和他的名字关联起来
			else new_slot_in_env(sc, sc->code, sc->ret_value);
			s_return(sc,sc->code);

		case OP_DELAY:      /* delay */ //delay就是吧表达式转化为一个无参数的闭包
			//形式  (delay (expr ...))   
			//例子 (define f (delay (+ 1 1))) (f)
			//例子 (define f (delay 1)) (f)
			x = mk_closure(sc, cons(sc, &g_nil, sc->code), sc->envir);
			typeflag(x)=T_PROMISE;
			s_return(sc,x);

		case OP_PAPPLY:     /* apply */
			//例子 (apply + '(1 2 3))
			sc->code = car(sc->args);
			sc->args = cadr(sc->args);
			s_goto(sc,OP_APPLY);
		case OP_PEVAL: /* eval */ 
			//形式(eval code envir)
			if(cdr(sc->args)!=&g_nil) sc->envir=cadr(sc->args);//设置环境
			sc->code = car(sc->args);//要执行的代码
			s_goto(sc,OP_EVAL);
		case OP_CONTINUATION:    /* call-with-current-continuation */
			//将当前堆栈作为参数传给 作为过程的call/cc的参数
			sc->code = car(sc->args);
			sc->args = cons(sc, mk_continuation(sc, sc->call_stack), &g_nil);
			s_goto(sc,OP_APPLY);
		default:
			_snprintf(sc->strbuff,STR_BUFF_SIZE,"%d: illegal operator", sc->op);
			Error0(sc,sc->strbuff);
	}
	return &g_true;
}

static cell_t* opexe_2(scheme *sc, opcode op) {
	cell_t* x;
	num_t v;
	double dd;
	switch (op) {
		case OP_INEX2EX:    /* inexact->exact */ //将一个数字（整型或浮点型）无损的转化为整型
			x=car(sc->args);
			if(x->_num.is_fix) {
				s_return(sc,x);
			} else if(modf(x->_num.f,&dd)==0.0) {
				s_return(sc,mk_integer(sc,ivalue(x)));
			} else {
				Error1(sc,"inexact->exact: not integral:",x);
			}
		case OP_EXP://自然数的x次方
			x=car(sc->args);
			s_return(sc, mk_real(sc, exp(rvalue(x))));
		case OP_LOG:
			x=car(sc->args);
			s_return(sc, mk_real(sc, log(rvalue(x))));
		case OP_SIN:
			x=car(sc->args);
			s_return(sc, mk_real(sc, sin(rvalue(x))));
		case OP_COS:
			x=car(sc->args);
			s_return(sc, mk_real(sc, cos(rvalue(x))));
		case OP_TAN:
			x=car(sc->args);
			s_return(sc, mk_real(sc, tan(rvalue(x))));
		case OP_ASIN:
			x=car(sc->args);
			s_return(sc, mk_real(sc, asin(rvalue(x))));
		case OP_ACOS:
			x=car(sc->args);
			s_return(sc, mk_real(sc, acos(rvalue(x))));
		case OP_ATAN:
			x=car(sc->args);
			if(cdr(sc->args)==&g_nil) {
				s_return(sc, mk_real(sc, atan(rvalue(x))));
			} else {
				cell_t* y=cadr(sc->args);
				s_return(sc, mk_real(sc, atan2(rvalue(x),rvalue(y))));
			}
		case OP_SQRT:
			x=car(sc->args);
			s_return(sc, mk_real(sc, sqrt(rvalue(x))));
		case OP_EXPT: {//求x的y次方
			double result;
			int real_result=1;
			cell_t* y=cadr(sc->args);
			x=car(sc->args);
			if (x->_num.is_fix&& y->_num.is_fix)
				real_result=0;
			/* This 'if' is an R5RS compatibility fix. */
			/* NOTE: Remove this 'if' fix for R6RS.    */
			if (rvalue(x) == 0 && rvalue(y) < 0) {
				result = 0.0;
			} else {
				result = pow(rvalue(x),rvalue(y));
			}
			/* Before returning integer result make sure we can. */
			/* If the test fails, result is too big for integer. */
			if (!real_result)
			{
				long result_as_long = (long)result;//如果result有小数位，必然导致result_as_long和result不相等
				if (result != (double)result_as_long) real_result = 1;
			}
			if (real_result) {
				s_return(sc, mk_real(sc, result));
			} else {
				s_return(sc, mk_integer(sc, (long)result));
			}
		}
		case OP_FLOOR:
			x=car(sc->args);
			s_return(sc, mk_real(sc, floor(rvalue(x))));
		case OP_CEILING:
			x=car(sc->args);
			s_return(sc, mk_real(sc, ceil(rvalue(x))));
		case OP_TRUNCATE : {
			double rvalue_of_x ;
			x=car(sc->args);
			rvalue_of_x = rvalue(x) ;
			if (rvalue_of_x > 0) {
				s_return(sc, mk_real(sc, floor(rvalue_of_x)));
			} else {
				s_return(sc, mk_real(sc, ceil(rvalue_of_x)));
			}
		}
		case OP_ROUND:
			x=car(sc->args);
			if (x->_num.is_fix) s_return(sc, x);
			s_return(sc, mk_real(sc, round_per_r5rs(rvalue(x))));
		case OP_ADD:        /* + */
			v=g_zero;
			for (x = sc->args; x != &g_nil; x = cdr(x)) {
				v=num_add(v,nvalue(car(x)));
			}
			s_return(sc,mk_number(sc, v));
		case OP_MUL:        /* * */
			v=g_one;
			for (x = sc->args; x != &g_nil; x = cdr(x)) {
				v=num_mul(v,nvalue(car(x)));
			}
			s_return(sc,mk_number(sc, v));
		case OP_SUB:        /* - */
			if(cdr(sc->args)==&g_nil) {
				x=sc->args;
				v=g_zero;
			} else {
				x = cdr(sc->args);
				v = nvalue(car(sc->args));
			}
			for (; x != &g_nil; x = cdr(x)) {
				v=num_sub(v,nvalue(car(x)));
			}
			s_return(sc,mk_number(sc, v));
		case OP_DIV:        /* / */
			if(cdr(sc->args)==&g_nil) {
				x=sc->args;
				v=g_one;
			} else {
				x = cdr(sc->args);
				v = nvalue(car(sc->args));
			}
			for (; x != &g_nil; x = cdr(x)) {
				if (!is_zero_double(rvalue(car(x))))
					v=num_div(v,nvalue(car(x)));
				else {
					Error0(sc,"/: division by zero");
				}
			}
			s_return(sc,mk_number(sc, v));
		case OP_INTDIV:        /* quotient */
			if(cdr(sc->args)==&g_nil) {
				x=sc->args;
				v=g_one;
			} else {
				x = cdr(sc->args);
				v = nvalue(car(sc->args));
			}
			for (; x != &g_nil; x = cdr(x)) {
				if (ivalue(car(x)) != 0)
					v=num_intdiv(v,nvalue(car(x)));
				else {
					Error0(sc,"quotient: division by zero");
				}
			}
			s_return(sc,mk_number(sc, v));
		case OP_REM:        /* remainder */
			v = nvalue(car(sc->args));
			if (ivalue(cadr(sc->args)) != 0)
				v=num_rem(v,nvalue(cadr(sc->args)));
			else {
				Error0(sc,"remainder: division by zero");
			}
			s_return(sc,mk_number(sc, v));
		case OP_MOD:        /* modulo */
			v = nvalue(car(sc->args));
			if (ivalue(cadr(sc->args)) != 0)
				v=num_mod(v,nvalue(cadr(sc->args)));
			else {
				Error0(sc,"modulo: division by zero");
			}
			s_return(sc,mk_number(sc, v));
		case OP_CAR:        /* car */
			s_return(sc,caar(sc->args));
		case OP_CDR:        /* cdr */
			s_return(sc,cdar(sc->args));
		case OP_CONS:       /* cons */ //生成点对 
			cdr(sc->args) = cadr(sc->args);
			s_return(sc,sc->args);
		case OP_SETCAR:     /* set-car! */
			if(!is_immutable(car(sc->args))) {
				caar(sc->args) = cadr(sc->args);
				s_return(sc,car(sc->args));
			} else {
				Error0(sc,"set-car!: unable to alter immutable pair");
			}
		case OP_SETCDR:     /* set-cdr! */
			if(!is_immutable(car(sc->args))) {
				cdar(sc->args) = cadr(sc->args);
				s_return(sc,car(sc->args));
			} else {
				Error0(sc,"set-cdr!: unable to alter immutable pair");
			}
		case OP_CHAR2INT: { /* char->integer */
			char c=(char)ivalue(car(sc->args));
			s_return(sc,mk_integer(sc,(unsigned char)c));
		}
		case OP_INT2CHAR: { /* integer->char */
			unsigned char c=(unsigned char)ivalue(car(sc->args));
			s_return(sc,mk_character(sc,(char)c));
		}
		case OP_CHARUPCASE: {
			unsigned char c=(unsigned char)ivalue(car(sc->args));
			c=toupper(c);
			s_return(sc,mk_character(sc,(char)c));
		}
		case OP_CHARDNCASE: {
			unsigned char c=(unsigned char)ivalue(car(sc->args));
			c=tolower(c);
			s_return(sc,mk_character(sc,(char)c));
		}
		case OP_STR2SYM:  /* string->symbol */
			s_return(sc,mk_symbol(sc,string_value(car(sc->args))));
		case OP_STR2ATOM: /* string->atom */ {
			char *s=string_value(car(sc->args));
			long pf = 0;
			if(cdr(sc->args)!=&g_nil) {
				/* we know cadr(sc->args) is a natural number */
				/* see if it is 2, 8, 10, or 16, or error */
				pf = ivalue_unchecked(cadr(sc->args));
				if(pf == 16 || pf == 10 || pf == 8 || pf == 2) {
					/* base is OK */
				}
				else {
					pf = -1;
				}
			}
			if (pf < 0) {
				Error1(sc, "string->atom: bad base:", cadr(sc->args));
			} else if(*s=='#') /* no use of base! */ {
				s_return(sc, mk_sharp_const(sc, s+1));
			} else {
				if (pf == 0 || pf == 10) {
					s_return(sc, mk_atom_from_string(sc, s));
				}
				else {
					char *ep;
					long iv = strtol(s,&ep,(int )pf);
					if (*ep == 0) {
						s_return(sc, mk_integer(sc, iv));
					}
					else {
						s_return(sc, &g_false);
					}
				}
			}
		}
		case OP_SYM2STR: /* symbol->string */
			x=mk_string(sc,sym_name(car(sc->args)));
			setimmutable(x);
			s_return(sc,x);
		case OP_ATOM2STR: /* atom->string */ {
				long print_flag = 0;
				x=car(sc->args);
				if(cdr(sc->args)!=&g_nil) {
					/* we know cadr(sc->args) is a natural number */
					/* see if it is 2, 8, 10, or 16, or error */
					print_flag = ivalue_unchecked(cadr(sc->args));
					if(is_number(x) && (print_flag == 16 || print_flag == 10 || print_flag == 8 || print_flag == 2)) {
						/* base is OK */
					}
					else print_flag = -1;
				}
				if (print_flag < 0) {
					Error1(sc, "atom->string: bad base:", cadr(sc->args));
				} else if(is_number(x) || is_character(x) || is_string(x) || is_symbol(x)) {
					char *p;
					int len;
					atom2str(sc,x,(int )print_flag,&p,&len);
					s_return(sc,mk_string_n(sc,p,len));
				} else {
					Error1(sc, "atom->string: not an atom:", x);
				}
			}
		case OP_MKSTRING: { /* make-string */
			int len=ivalue(car(sc->args));
			int fill=' ';
			if(cdr(sc->args)!=&g_nil) {
				fill=char_value(cadr(sc->args));
			}
			s_return(sc,mk_empty_string(sc,len,(char)fill));
		}
		case OP_STRLEN:  /* string-length */
			s_return(sc,mk_integer(sc,string_len(car(sc->args))));
		case OP_STRREF: { /* string-ref */
			char *str=string_value(car(sc->args));
			int index=ivalue(cadr(sc->args));
			if(index>=string_len(car(sc->args))) {
				Error1(sc,"string-ref: out of bounds:",cadr(sc->args));
			}
			s_return(sc,mk_character(sc,((unsigned char*)str)[index]));
		}
		case OP_STRSET: { /* string-set! */
			if(is_immutable(car(sc->args))) {
				Error1(sc,"string-set!: unable to alter immutable string:",car(sc->args));
			}
			char *str=string_value(car(sc->args));
			int index=ivalue(cadr(sc->args));
			if(index>=string_len(car(sc->args))) {
				Error1(sc,"string-set!: out of bounds:",cadr(sc->args));
			}
			int c=char_value(caddr(sc->args));
			str[index]=(char)c;
			s_return(sc,car(sc->args));
		}
		case OP_STRAPPEND: { /* string-append */
			/* in 1.29 string-append was in Scheme in init.scm but was too slow */
			int len = 0;
			/* compute needed length for new string */
			for (x = sc->args; x != &g_nil; x = cdr(x)) {
				len += string_len(car(x));
			}
			cell_t* newstr = mk_empty_string(sc, len, ' ');
			/* store the contents of the argument strings into the new string */
			char *pos = string_value(newstr);
			for (x = sc->args ;  x != &g_nil ; pos += string_len(car(x)), x = cdr(x)) {
					memcpy(pos, string_value(car(x)), string_len(car(x)));
			}
			s_return(sc, newstr);
		}
		case OP_SUBSTR: { /* substring */
			char *str=string_value(car(sc->args));
			int begin=ivalue(cadr(sc->args));
			if(begin>string_len(car(sc->args))) {
				Error1(sc,"substring: start out of bounds:",cadr(sc->args));
			}
			int end;
			if(cddr(sc->args)!=&g_nil) {
				end=ivalue(caddr(sc->args));
				if(end>string_len(car(sc->args)) || end<begin) {
					Error1(sc,"substring: end out of bounds:",caddr(sc->args));
				}
			} else {
				end=string_len(car(sc->args));
			}
			int len=end-begin;
			x=mk_empty_string(sc,len,' ');
			memcpy(string_value(x),str+begin,len);
			string_value(x)[len]=0;
			s_return(sc,x);
		}
		case OP_VECTOR: {   /* vector */
			int len=list_length(sc,sc->args);
			if(len<0) Error1(sc,"vector: not a proper list:",sc->args);
			cell_t* vec=mk_vector(sc,len);
			int  index = 0;
			for (x = sc->args; is_pair(x); x = cdr(x), index++) {
				set_vector_item(vec,index,car(x));
			}
			s_return(sc,vec);
		}
		case OP_MKVECTOR: { /* make-vector */
				int len=ivalue(car(sc->args));
				cell_t* vec=mk_vector(sc,len);
				if(cdr(sc->args)!=&g_nil) {
					fill_vector(vec,cadr(sc->args));
				}
				s_return(sc,vec);
			}
		case OP_VECLEN:  /* vector-length */
			s_return(sc,mk_integer(sc,ivalue(car(sc->args))));
		case OP_VECREF: { /* vector-ref */
			int index=ivalue(cadr(sc->args));
			if(index>=ivalue(car(sc->args))) {
				Error1(sc,"vector-ref: out of bounds:",cadr(sc->args));
			}
			s_return(sc,get_vector_item(car(sc->args),index));
		}
		case OP_VECSET: {   /* vector-set! */
			if(is_immutable(car(sc->args))) {
				Error1(sc,"vector-set!: unable to alter immutable vector:",car(sc->args));
			}
			int index=ivalue(cadr(sc->args));
			if(index>=ivalue(car(sc->args))) {
				Error1(sc,"vector-set!: out of bounds:",cadr(sc->args));
			}
			set_vector_item(car(sc->args),index,caddr(sc->args));
			s_return(sc,car(sc->args));
		}
		default:
			_snprintf(sc->strbuff,STR_BUFF_SIZE,"%d: illegal operator", sc->op);
			Error0(sc,sc->strbuff);
	}
	return &g_true;
}

static cell_t* opexe_3(scheme *sc, opcode op) {
	cell_t* x;
	num_t v;
	int (*comp_func)(num_t,num_t)=0;
	switch (op) {
		case OP_NOT:        /* not */
			s_retbool(is_false(car(sc->args)));
		case OP_BOOLP:       /* boolean? */
			s_retbool(car(sc->args) == &g_false || car(sc->args) == &g_true);
		case OP_EOFOBJP:       /* boolean? */
			s_retbool(car(sc->args) == &g_eof);
		case OP_NULLP:       /* null? */
			s_retbool(car(sc->args) == &g_nil);
		case OP_NUMEQ:      /* = */
		case OP_LESS:       /* < */
		case OP_GRE:        /* > */
		case OP_LEQ:        /* <= */
		case OP_GEQ:        /* >= */
			switch(op) {
				case OP_NUMEQ: comp_func=num_eq; break;
				case OP_LESS:  comp_func=num_lt; break;
				case OP_GRE:   comp_func=num_gt; break;
				case OP_LEQ:   comp_func=num_le; break;
				case OP_GEQ:   comp_func=num_ge; break;
			}
			x=sc->args;
			v=nvalue(car(x));
			for (x=cdr(x); x != &g_nil; x = cdr(x)) {
				if(!comp_func(v,nvalue(car(x)))) {
					s_retbool(0);
				}
				v=nvalue(car(x));
			}
			s_retbool(1);
		case OP_SYMBOLP:     /* symbol? */
			s_retbool(is_symbol(car(sc->args)));
		case OP_NUMBERP:     /* number? */
			s_retbool(is_number(car(sc->args)));
		case OP_STRINGP:     /* string? */
			s_retbool(is_string(car(sc->args)));
		case OP_INTEGERP:     /* integer? */
			s_retbool(is_integer(car(sc->args)));
		case OP_REALP:     /* real? */
			s_retbool(is_number(car(sc->args))); /* All numbers are real */
		case OP_CHARP:     /* char? */
			s_retbool(is_character(car(sc->args)));
		case OP_CHARAP:     /* char-alphabetic? */
			s_retbool(isalphax(ivalue(car(sc->args))));
		case OP_CHARNP:     /* char-numeric? */
			s_retbool(isdigitx(ivalue(car(sc->args))));
		case OP_CHARWP:     /* char-whitespace? */
			s_retbool(isspacex(ivalue(car(sc->args))));
		case OP_CHARUP:     /* char-upper-case? */
			s_retbool(isupperx(ivalue(car(sc->args))));
		case OP_CHARLP:     /* char-lower-case? */
			s_retbool(islowerx(ivalue(car(sc->args))));
		case OP_PORTP:     /* port? */
			s_retbool(is_port(car(sc->args)));
		case OP_INPORTP:     /* input-port? */
			s_retbool(is_inport(car(sc->args)));
		case OP_OUTPORTP:     /* output-port? */
			s_retbool(is_outport(car(sc->args)));
		case OP_PROCP:       /* procedure? */
			/*continuation should be procedure by the example
			* (call-with-current-continuation procedure?) ==> #t
			* in R^3 report sec. 6.9*/
			s_retbool(is_proc(car(sc->args)) || is_closure(car(sc->args))
				|| is_continuation(car(sc->args)) || is_foreign(car(sc->args)));
		case OP_PAIRP:       /* pair? */
			s_retbool(is_pair(car(sc->args)));
		case OP_LISTP:       /* list? */
			s_retbool(list_length(sc,car(sc->args)) >= 0);
		case OP_ENVP:        /* environment? */
			s_retbool(is_environment(car(sc->args)));
		case OP_VECTORP:     /* vector? */
			s_retbool(is_vector(car(sc->args)));
		case OP_EQ:         /* eq? */
			s_retbool(car(sc->args) == cadr(sc->args));
		case OP_EQV:        /* eqv? */
			s_retbool(eqv(car(sc->args), cadr(sc->args)));
		default:
			_snprintf(sc->strbuff,STR_BUFF_SIZE,"%d: illegal operator", sc->op);
			Error0(sc,sc->strbuff);
	}
	return &g_true;
}

static cell_t* opexe_4(scheme *sc, opcode op) {
	cell_t* x, *y;
	switch (op) {
		case OP_FORCE:      /* force */
			sc->code = car(sc->args);
			if (is_promise(sc->code)) {
				/* Should change type to closure here */
				s_save(sc, OP_SAVE_FORCED, &g_nil, sc->code);
				sc->args = &g_nil;
				s_goto(sc,OP_APPLY);
			} 
			else s_return(sc,sc->code);
		case OP_SAVE_FORCED:     /* Save forced value replacing promise */
			memcpy(sc->code,sc->ret_value,sizeof(struct cell_t));
			s_return(sc,sc->ret_value);
		case OP_WRITE:      /* write */
		case OP_DISPLAY:    /* display */
		case OP_WRITE_CHAR: /* write-char */
			if(is_pair(cdr(sc->args))) {
				if(cadr(sc->args)!=sc->outport) {
					x=cons(sc,sc->outport,&g_nil);
					s_save(sc,OP_SET_OUTPORT, x, &g_nil);
					sc->outport=cadr(sc->args);
				}
			}
			sc->args = car(sc->args);
			if(op==OP_WRITE) sc->print_flag = 1;
			else sc->print_flag = 0;
			s_goto(sc,OP_P0LIST);
		case OP_NEWLINE:    /* newline */
			if(is_pair(sc->args)) {
				if(car(sc->args)!=sc->outport) {
					x=cons(sc,sc->outport,&g_nil);
					s_save(sc,OP_SET_OUTPORT, x, &g_nil);
					sc->outport=car(sc->args);
				}
			}
			write_string(sc, "\n");
			s_return(sc,&g_true);

		case OP_ERR0:  /* error */
			sc->eval_result=-1;
			if (!is_string(car(sc->args))) {
				sc->args=cons(sc,mk_string(sc," -- "),sc->args);
				setimmutable(car(sc->args));
			}
			write_string(sc, "Error: ");
			write_string(sc, string_value(car(sc->args)));
			sc->args = cdr(sc->args);
			s_goto(sc,OP_ERR1);

		case OP_ERR1:  /* error */
			write_string(sc, " ");
			if (sc->args != &g_nil) {
				s_save(sc,OP_ERR1, cdr(sc->args), &g_nil);
				sc->args = car(sc->args);
				sc->print_flag = 1;
				s_goto(sc,OP_P0LIST);
			} else {
				write_string(sc, "\n");
				s_goto(sc,OP_T0LVL);//????????
				if(file_interactive(sc)){//??????????if(sc->file_interactive)
					s_goto(sc,OP_T0LVL);
				}
				else return &g_nil;
			}
		case OP_REVERSE:   /* reverse */
			s_return(sc,reverse(sc, car(sc->args)));
		case OP_LIST_STAR: /* list* */
			s_return(sc,list_star(sc,sc->args));
		case OP_APPEND:    /* append */
			x = &g_nil;
			y = sc->args;
			while (y != &g_nil) {
				x = revappend(sc, x, car(y));
				y = cdr(y);
				if (x == &g_false) {
					Error0(sc, "non-list argument to append");
				}
			}
			s_return(sc, reverse(sc, x));
		case OP_QUIT:       /* quit */
			if(is_pair(sc->args)) sc->eval_result=ivalue(car(sc->args));
			return &g_nil;
		case OP_GC:         /* gc */
			gc(sc, &g_nil, &g_nil);
			s_return(sc,&g_true);
		case OP_GCVERB:   /* gc-verbose */{ 
			int  was = sc->gc_verbose;
			sc->gc_verbose = (car(sc->args) != &g_false);
			s_retbool(was);
		}
		case OP_NEWSEGMENT: /* new-segment */
			if (!is_pair(sc->args) || !is_number(car(sc->args))) {
				Error0(sc,"new-segment: argument must be a number");
			}
			alloc_cellseg(sc, (int) ivalue(car(sc->args)));
			s_return(sc,&g_true);
		case OP_OBLIST: /* oblist */
			s_return(sc, oblist_all_symbols(sc));
		case OP_CURR_INPORT: /* current-input-port */
			s_return(sc,sc->inport);
		case OP_CURR_OUTPORT: /* current-output-port */
			s_return(sc,sc->outport);
		case OP_OPEN_INFILE: /* open-input-file */
		case OP_OPEN_OUTFILE: /* open-output-file */
		case OP_OPEN_INOUTFILE: /* open-input-output-file */ {
			int prop=0;
			switch(op) {
				case OP_OPEN_INFILE:
					prop=port_input; 
					break;
				case OP_OPEN_OUTFILE:
					prop=port_output; 
					break;
				case OP_OPEN_INOUTFILE:
					prop=port_input|port_output;
					break;
			}
			cell_t* p=port_from_filename(sc,string_value(car(sc->args)),prop);
			if(p==&g_nil) s_return(sc,&g_false);
			else s_return(sc,p);
		}

		case OP_OPEN_INSTRING: /* open-input-string */
		case OP_OPEN_INOUTSTRING: /* open-input-output-string */ {
			int prop=0;
			switch(op) {
				case OP_OPEN_INSTRING:     
					prop=port_input; 
					break;
				case OP_OPEN_INOUTSTRING:  
					prop=port_input|port_output; 
					break;
			}
			cell_t* p=port_from_string(sc, string_value(car(sc->args)),
				string_value(car(sc->args))+string_len(car(sc->args)), prop);
			if(p==&g_nil) s_return(sc,&g_false);
			else s_return(sc,p);
		}
		case OP_OPEN_OUTSTRING: /* open-output-string */ {
			cell_t* p;
			if(car(sc->args)==&g_nil) {
				p=port_from_string(sc, NULL, NULL,port_output|port_can_realloc);//分配一片空的内存做为输出端口
			} else {
				p=port_from_string(sc, string_value(car(sc->args)),
					string_value(car(sc->args))+string_len(car(sc->args)),
					port_output);
			}
			if(p==&g_nil) s_return(sc,&g_false);
			else s_return(sc,p);
		}
		case OP_GET_OUTSTRING: /* get-output-string */ {
			port_t *p=car(sc->args)->_port;
			if (p->kind&port_string) {
				s_return(sc,mk_string_n(sc,p->s.start,p->s.curr-p->s.start));
			}
			s_return(sc,&g_false);
		}
		case OP_CLOSE_INPORT: /* close-input-port */
			port_close(sc,car(sc->args),port_input);
			s_return(sc,&g_true);

		case OP_CLOSE_OUTPORT: /* close-output-port */
			port_close(sc,car(sc->args),port_output);
			s_return(sc,&g_true);

		case OP_INT_ENV: /* interaction-environment */
			s_return(sc,sc->global_env);

		case OP_CURR_ENV: /* current-environment */
			s_return(sc,sc->envir);
	}
	return &g_true;
}

static cell_t* opexe_5(scheme *sc, opcode op) {
	cell_t* x;
	if(sc->nesting!=0) {
		int n=sc->nesting;
		sc->nesting=0;
		sc->eval_result=-1;
		Error1(sc,"unmatched parentheses:",mk_integer(sc,n));//未匹配的圆括号
	}
	switch (op) {
		case OP_READ:
			if(is_pair(sc->args))
			{
				if(!is_inport(car(sc->args))) {
					Error1(sc,"read: not an input port:",car(sc->args));
				}
				if(car(sc->args)!=sc->inport) {
					x=cons(sc,sc->inport,&g_nil);
					s_save(sc,OP_SET_INPORT, x, &g_nil);
					sc->inport=car(sc->args);
				}
			}
			s_goto(sc,OP_READ_INTERNAL);
		case OP_READ_CHAR: /* read-char */
		case OP_PEEK_CHAR: /* peek-char */ {
			if(is_pair(sc->args)) {
				if(car(sc->args)!=sc->inport) {
					x=cons(sc,sc->inport,&g_nil);
					s_save(sc,OP_SET_INPORT, x, &g_nil);
					sc->inport=car(sc->args);
				}
			}
			int c=get_char(sc);
			if(sc->op==OP_PEEK_CHAR) unget_char(sc,c);
			if(c==EOF) s_return(sc,&g_eof);
			else s_return(sc,mk_character(sc,c));
		}
		case OP_CHAR_READY: /* char-ready? */ 
			x=sc->inport;
			if(is_pair(sc->args)) x=car(sc->args);
			s_retbool(x->_port->kind&port_string);
		case OP_SET_INPORT: /* set-input-port */
			sc->inport=car(sc->args);
			s_return(sc,sc->ret_value);
		case OP_SET_OUTPORT: /* set-output-port */
			sc->outport=car(sc->args);
			s_return(sc,sc->ret_value);
		case OP_RDSEXPR:
			switch (sc->tok) {
				case TOK_EOF:
					s_return(sc,&g_eof);
				case TOK_VECTOR:
					s_save(sc,OP_RDVEC,&g_nil,&g_nil);//压入 数组 处理过程
					/* fall through */
				case TOK_LPAREN:
					sc->tok = token(sc);
					if (sc->tok == TOK_RPAREN) {
						s_return(sc,&g_nil);
					} else if (sc->tok == TOK_DOT) {
						Error0(sc,"syntax error: illegal dot expression");
					} else {
						sc->nesting_stack[sc->top_file_index]++;
						s_save(sc,OP_RDLIST, &g_nil, &g_nil);//压入读取列表的函数
						s_goto(sc,OP_RDSEXPR);//读取S表达式
					}
				case TOK_QUOTE://引用
					s_save(sc,OP_RDQUOTE, &g_nil, &g_nil);//压入 引用 处理函数
					sc->tok = token(sc);
					s_goto(sc,OP_RDSEXPR);//读取S表达式
				case TOK_BQUOTE://准引用
					sc->tok = token(sc);
					if(sc->tok==TOK_VECTOR) {
						s_save(sc,OP_RDQQUOTEVEC, &g_nil, &g_nil);//压入 解引用数组 处理过程
						sc->tok=TOK_LPAREN;//这里替换成了TOK_LPAREN ，就不会压入TOK_VECTOR的处理函数
						s_goto(sc,OP_RDSEXPR);//读取S表达式 这里会转向读取一个列表的处理过程
					} else {
						s_save(sc,OP_RDQQUOTE, &g_nil, &g_nil);//压入 准引用 处理过程
					}
					s_goto(sc,OP_RDSEXPR);//读取S表达式
				case TOK_COMMA://,解引用 
					s_save(sc,OP_RDUNQUOTE, &g_nil, &g_nil);//压入执行,操作的代码
					sc->tok = token(sc);
					s_goto(sc,OP_RDSEXPR);//读取S表达式
				case TOK_ATMARK://,@解引用 
					s_save(sc,OP_RDUQTSP, &g_nil, &g_nil);//压入执行,@操作的代码
					sc->tok = token(sc);
					s_goto(sc,OP_RDSEXPR);//读取S表达式
				case TOK_ATOM://原子
					s_return(sc,mk_atom_from_string(sc, readstr_upto(sc, DELIMITERS)));
				case TOK_DQUOTE://双引号 (字符串类型的原子)
					x=readstrexp(sc);
					if(x==&g_false) Error0(sc,"Error reading string");
					setimmutable(x);
					s_return(sc,x);
				case TOK_SHARP: {//#是eval的简写吗？
					cell_t* f=find_slot_in_env(sc,sc->envir,sc->sym_sharp_hook,1);//f的类型symbol_kv ,f是一段处理#的代码
					if(f==&g_nil) Error0(sc,"undefined sharp expression");
					sc->code=cons(sc,slot_value_in_env(f),&g_nil);
					s_goto(sc,OP_EVAL);
				}
				case TOK_SHARP_CONST://常量
					x = mk_sharp_const(sc, readstr_upto(sc, DELIMITERS));
					if(x==&g_nil) Error0(sc,"undefined const sharp expression");
					s_return(sc,x);
				default:
					Error0(sc,"syntax error: illegal token");
			}
			break;
		case OP_RDLIST: {
			sc->args = cons(sc, sc->ret_value, sc->args);
			sc->tok = token(sc);
			if (sc->tok == TOK_EOF) s_return(sc,&g_eof); 
			else if (sc->tok == TOK_RPAREN) {
				sc->nesting_stack[sc->top_file_index]--;
				s_return(sc,reverse(sc,  sc->args));
			} else if (sc->tok == TOK_DOT) {
				s_save(sc,OP_RDDOT, sc->args, &g_nil);
				sc->tok = token(sc);
				s_goto(sc,OP_RDSEXPR);
			} else {
				s_save(sc,OP_RDLIST, sc->args, &g_nil);;
				s_goto(sc,OP_RDSEXPR);
			}
		}
		case OP_RDVEC:
			sc->args=sc->ret_value;
			s_goto(sc,OP_VECTOR);
		case OP_RDDOT:
			if (token(sc) != TOK_RPAREN) {
				Error0(sc,"syntax error: illegal dot expression");
			} else {
				sc->nesting_stack[sc->top_file_index]--;
				s_return(sc,revappend(sc, sc->ret_value, sc->args));
			}
		case OP_RDQUOTE:
			s_return(sc,cons(sc, sc->sym_quote, cons(sc, sc->ret_value, &g_nil)));
		case OP_RDQQUOTE:
			s_return(sc,cons(sc, sc->sym_qquote, cons(sc, sc->ret_value, &g_nil)));
		case OP_RDQQUOTEVEC:
			//下面的代码会进行类似这样的一个操作 (apply vector `(,(+ 1 2) 4)) =>#(3 4)
			s_return(sc,cons(sc, mk_symbol(sc,"apply"),
				cons(sc, mk_symbol(sc,"vector"),
				cons(sc,cons(sc, sc->sym_qquote,cons(sc,sc->ret_value,&g_nil)),
				&g_nil))));
		case OP_RDUNQUOTE:
			s_return(sc,cons(sc, sc->sym_unquote, cons(sc, sc->ret_value, &g_nil)));
		case OP_RDUQTSP:
			s_return(sc,cons(sc, sc->sym_unquote_sp, cons(sc, sc->ret_value, &g_nil)));

			/* ========== printing part ========== */
		case OP_P0LIST:
			if(is_vector(sc->args)) {
				write_string(sc,"#(");
				sc->args=cons(sc,sc->args,mk_integer(sc,0));
				s_goto(sc,OP_PVECFROM);
			} else if(is_environment(sc->args)) {//环境
				write_string(sc,"#<ENVIRONMENT>");
				s_return(sc,&g_true);
			} else if (!is_pair(sc->args)) {//原子
				printatom(sc, sc->args, sc->print_flag);
				s_return(sc,&g_true);
			} else if (car(sc->args) == sc->sym_quote && ok_abbrev(cdr(sc->args))) {
				write_string(sc, "'");
				sc->args = cadr(sc->args);
				s_goto(sc,OP_P0LIST);
			} else if (car(sc->args) == sc->sym_qquote && ok_abbrev(cdr(sc->args))) {
				write_string(sc, "`");
				sc->args = cadr(sc->args);
				s_goto(sc,OP_P0LIST);
			} else if (car(sc->args) == sc->sym_unquote && ok_abbrev(cdr(sc->args))) {
				write_string(sc, ",");
				sc->args = cadr(sc->args);
				s_goto(sc,OP_P0LIST);
			} else if (car(sc->args) == sc->sym_unquote_sp && ok_abbrev(cdr(sc->args))) {
				write_string(sc, ",@");
				sc->args = cadr(sc->args);
				s_goto(sc,OP_P0LIST);
			} else {
				write_string(sc, "(");
				s_save(sc,OP_P1LIST, cdr(sc->args), &g_nil);
				sc->args = car(sc->args);
				s_goto(sc,OP_P0LIST);
			}
		case OP_P1LIST:
			if (is_pair(sc->args)) {
				s_save(sc,OP_P1LIST, cdr(sc->args), &g_nil);
				write_string(sc, " ");
				sc->args = car(sc->args);
				s_goto(sc,OP_P0LIST);
			} else if(sc->args != &g_nil){//这里处理数据位原子（包括数组）的情况
				s_save(sc,OP_P1LIST,&g_nil,&g_nil);
				write_string(sc, " . ");
				s_goto(sc,OP_P0LIST);
			} else {
				write_string(sc, ")");
				s_return(sc,&g_true);
			}
		case OP_PVECFROM: {
			int index=ivalue_unchecked(cdr(sc->args));
			cell_t* vec=car(sc->args);
			int len=ivalue_unchecked(vec);
			if(index==len) {
				write_string(sc,")");
				s_return(sc,&g_true);
			} else {
				cell_t* elem=get_vector_item(vec,index);
				ivalue_unchecked(cdr(sc->args))=index+1;
				s_save(sc,OP_PVECFROM, sc->args, &g_nil);
				sc->args=elem;
				if (index > 0) write_string(sc," ");
				s_goto(sc,OP_P0LIST);
			}
		}
		default:
			_snprintf(sc->strbuff,STR_BUFF_SIZE,"%d: illegal operator", sc->op);
			Error0(sc,sc->strbuff);
	}
	return &g_true;
}

static cell_t* opexe_6(scheme *sc, opcode op) {
	cell_t* x, *y;
	switch (op) {
		case OP_LIST_LENGTH:{     /* length */   /* a.k */
			long len=list_length(sc,car(sc->args));
			if(len<0) Error1(sc,"length: not a list:",car(sc->args));
			s_return(sc,mk_integer(sc, len));
		}
		case OP_ASSQ:       /* assq */     /* a.k */
			x = car(sc->args);
			for (y = cadr(sc->args); is_pair(y); y = cdr(y)) {
				if (!is_pair(car(y))) Error0(sc,"unable to handle non pair element");
				if (x == caar(y))
					break;
			}
			if (is_pair(y)) s_return(sc,car(y));
			else s_return(sc,&g_false);
		case OP_GET_CLOSURE:     /* get-closure-code */   /* a.k */
			sc->args = car(sc->args);
			if (sc->args == &g_nil) {
				s_return(sc,&g_false);
			} else if (is_closure(sc->args)) {
				s_return(sc,cons(sc, sc->sym_lambda, closure_code(sc->args)));
			} else if (is_macro(sc->args)) {
				s_return(sc,cons(sc, sc->sym_lambda, closure_code(sc->args)));
			} else {
				s_return(sc,&g_false);
			}
		case OP_CLOSUREP:        /* closure? */
			/* Note, macro object is also a closure.Therefore, (closure? <#MACRO>) ==> #t*/
			s_retbool(is_closure(car(sc->args)));
		case OP_MACROP:          /* macro? */
			s_retbool(is_macro(car(sc->args)));
		default:
			_snprintf(sc->strbuff,STR_BUFF_SIZE,"%d: illegal operator", sc->op);
			Error0(sc,sc->strbuff);
	}
	return &g_true; /* NOTREACHED */
}

//参数类型标记，用于声明方法的参数列表中参数的类型
#define TST_NONE 0
#define TST_ANY "\001"
#define TST_STRING "\002"
#define TST_SYMBOL "\003"
#define TST_PORT "\004"
#define TST_INPORT "\005"
#define TST_OUTPORT "\006"
#define TST_ENVIRONMENT "\007"
#define TST_PAIR "\010"
#define TST_LIST "\011"
#define TST_CHAR "\012"
#define TST_VECTOR "\013"
#define TST_NUMBER "\014"
#define TST_INTEGER "\015"
#define TST_NATURAL "\016"

op_code_info g_dispatch_table[]= {
#define _OP_DEF(A,B,C,D,E,OP) {A,B,C,D,E},
#include "opdefines.h"
	{ 0 }
};

static const char *proc_name(cell_t* x) {
	int n=proc_value(x);
	const char *name=g_dispatch_table[n].name;
	if(name==0) name="ILLEGAL!";
	return name;
}

static cell_t* mk_proc(scheme *sc, opcode op) {
	cell_t* p = mk_cell(sc, &g_nil, &g_nil);
	typeflag(p) = (T_PROC | T_ATOM);
	inital_num(&p->_num,(long)op);
	return p;
}

static void add_syntax_symbol(scheme *sc, char *name) {
	cell_t* sym = mk_symbol(sc, name);
	typeflag(sym) |= T_SYNTAX;
}

/* Hard-coded for the given keywords. Remember to rewrite if more are added! */
static int syntax_sym2opcode(cell_t* p) {
	const char *s=string_value(car(p));
	switch(string_len(car(p))) {
		case 2:
			if(s[0]=='i') return OP_IF0;				/* if */
			else return OP_OR0;						/* or */
		case 3:
			if(s[0]=='a') return OP_AND0;		/* and */
			else return OP_LET0;						/* let */
		case 4:
			switch(s[3]) {
		case 'e': return OP_CASE0;			/* case */
		case 'd': return OP_COND0;		/* cond */
		case '*': return OP_LETSTAR0;		/* let* */
		default: return OP_SET0;			/* set! */
			}
		case 5:
			switch(s[2]) {
		case 'g': return OP_BEGIN;		/* begin */
		case 'l': return OP_DELAY;			/* delay */
		case 'c': return OP_MACRO0;		/* macro */
		default: return OP_QUOTE;		/* quote */
			}
		case 6:
			switch(s[2]) {
		case 'm': return OP_LAMBDA;	/* lambda */
		case 'f': return OP_DEF0;			/* define */
		default: return OP_LET0REC;		/* letrec */
			}
		default:
			return OP_C0STREAM;					/* cons-stream */
	}
}

typedef int (*test_predicate_t)(cell_t*);
static int is_any(cell_t* p) { return 1;}
static int is_nonneg(cell_t* p) {return  is_integer(p) && (ivalue(p)>=0);}//判断是不是整数，并且大于等于0
static int is_pair_ex(cell_t* p)
{
	if(p==&g_nil) return 1;
	if(is_pair(p)) return 1;
	return 0;
}
/* Correspond carefully with following defines! */
//这个结构用于辅助参数检查
static struct {
	test_predicate_t fct;
	const char *kind;
} g_type_check_funs[]={
	{0,0}, /* unused */
	{is_any, 0},
	{is_string, "string"},
	{is_symbol, "symbol"},
	{is_port, "port"},
	{is_inport,"input port"},
	{is_outport,"output port"},
	{is_environment, "environment"},
	{is_pair, "pair"},
	{is_pair_ex, "pair or '()"},
	{is_character, "character"},
	{is_vector, "vector"},
	{is_number, "number"},
	{is_integer, "integer"},
	{is_nonneg, "non-negative integer"}
};

bool check_arg_type(scheme *sc,char* msg)
{
	op_code_info *pcd=g_dispatch_table+sc->op;
	if (pcd->name!=0) { /* if built-in function, check arguments */
		int n=list_length(sc,sc->args);

		/* Check number of arguments */
		if(n<pcd->min_arity) {//检查是否小于需要的最小参数个数
			_snprintf(msg, STR_BUFF_SIZE, "%s: needs%s %d argument(s)",
				pcd->name,
				pcd->min_arity==pcd->max_arity?"":" at least",
				pcd->min_arity);
			return false;
		}
		if(n>pcd->max_arity) {//检查是否大于需要的最大参数个数
			_snprintf(msg, STR_BUFF_SIZE, "%s: needs%s %d argument(s)",
				pcd->name,
				pcd->min_arity==pcd->max_arity?"":" at most",
				pcd->max_arity);
			return false;
		}
		if(pcd->args_type!=0) {
			//检查参数类型
			int arg_index=0;
			const char *type_info=pcd->args_type;
			cell_t* args=sc->args;
			do {
				cell_t* arg=car(args);
				if(!g_type_check_funs[type_info[0]].fct(arg)) break;
				if(type_info[1]!=0) type_info++;/* last test is replicated as necessary */ //最后一个类型用于重复检查剩余的参数
				args=cdr(args);
				arg_index++;
			} while(arg_index<n);
			if(arg_index<n) {
				_snprintf(msg, STR_BUFF_SIZE, "%s: argument %d must be: %s",
					pcd->name,
					arg_index+1,
					g_type_check_funs[type_info[0]].kind);
				return false;
			}
		}
	}
	return true;
}

static void eval_cycle(scheme *sc, opcode op) {
	sc->op = op;
	for (;;) {
		char msg[STR_BUFF_SIZE];
		if(!check_arg_type(sc,msg)) {
			if(error_helper(sc,msg,0)==&g_nil) return;
		}
		op_code_info *pcd=g_dispatch_table+sc->op;
		if (pcd->func(sc, (opcode)sc->op) == &g_nil) return;
	}
}

void scheme_load_file(scheme *sc, FILE *fin, const char *filename) {
	sc->call_stack = &g_nil;
	sc->envir = sc->global_env;
	sc->top_file_index=0;
	sc->load_stack[0].kind=port_input|port_file;
	sc->load_stack[0].f.file=fin;
	if(filename) sc->load_stack[0].f.filename = store_string(sc, strlen(filename), filename, 0);
	sc->load_stack[0].f.curr_line = 0;
	sc->loadport=mk_port(sc,sc->load_stack);
	sc->inport=sc->loadport;

	sc->eval_result=0;
	sc->args = mk_integer(sc,sc->top_file_index);
	eval_cycle(sc, OP_T0LVL);
	typeflag(sc->loadport)=T_ATOM;
	if(sc->eval_result==0) sc->eval_result=sc->nesting!=0;
}

void scheme_load_string(scheme *sc, const char *cmd) {
	sc->call_stack = &g_nil;
	sc->envir = sc->global_env;
	sc->top_file_index=0;
	sc->load_stack[0].kind=port_input|port_string;
	sc->load_stack[0].s.start=(char*)cmd; /* This func respects const */
	sc->load_stack[0].s.end=(char*)cmd+strlen(cmd);
	sc->load_stack[0].s.curr=(char*)cmd;
	sc->loadport=mk_port(sc,sc->load_stack);
	sc->inport=sc->loadport;

	sc->eval_result=0;
	sc->args = mk_integer(sc,sc->top_file_index);
	eval_cycle(sc, OP_T0LVL);
	typeflag(sc->loadport)=T_ATOM;
	if(sc->eval_result==0) sc->eval_result=sc->nesting!=0;
}

int scheme_init(scheme *sc, func_alloc malloc_f, func_dealloc free_f) {
	inital_num(&g_zero,0L);
	inital_num(&g_one,1L);

	typeflag(&g_nil) = (T_ATOM | REF_MARK);
	car(&g_nil) = cdr(&g_nil) = &g_nil;
	typeflag(&g_true) = (T_ATOM | REF_MARK);
	car(&g_true) = cdr(&g_true) = &g_true;
	typeflag(&g_false) = (T_ATOM | REF_MARK);
	car(&g_false) = cdr(&g_false) = &g_false;

	sc->malloc=malloc_f;
	sc->free=free_f;
	sc->last_cell_seg = -1;
	sc->free_cell = &g_nil;
	sc->free_cell_count = 0;
	alloc_cellseg(sc,3);

	sc->outport=port_from_file(sc,stdout,port_output);
	sc->inport=port_from_file(sc,stdin,port_input);
	sc->save_inport=&g_nil;
	sc->loadport=&g_nil;
	sc->top_file_index=0;
	sc->nesting=0;

	sc->code = &g_nil;
	sc->call_stack = &g_nil;

	sc->gc_verbose = 0;

	sc->oblist = oblist_initial_value(sc);
	/* init global_env */
	new_frame_in_env(sc, &g_nil);
	sc->global_env = sc->envir;

	add_syntax_symbol(sc, "lambda");
	add_syntax_symbol(sc, "quote");
	add_syntax_symbol(sc, "define");
	add_syntax_symbol(sc, "if");
	add_syntax_symbol(sc, "begin");
	add_syntax_symbol(sc, "set!");
	add_syntax_symbol(sc, "let");
	add_syntax_symbol(sc, "let*");
	add_syntax_symbol(sc, "letrec");
	add_syntax_symbol(sc, "cond");
	add_syntax_symbol(sc, "delay");
	add_syntax_symbol(sc, "and");
	add_syntax_symbol(sc, "or");
	add_syntax_symbol(sc, "cons-stream");
	add_syntax_symbol(sc, "macro");
	add_syntax_symbol(sc, "case");

	/* initialization of global cell*s to special symbols */
	sc->sym_lambda = mk_symbol(sc, "lambda");
	sc->sym_quote = mk_symbol(sc, "quote");
	sc->sym_qquote = mk_symbol(sc, "quasiquote");
	sc->sym_unquote = mk_symbol(sc, "unquote");
	sc->sym_unquote_sp = mk_symbol(sc, "unquote-splicing");
	sc->sym_feed_to = mk_symbol(sc, "=>");
	sc->sym_colon_hook = mk_symbol(sc,"*colon-hook*");
	sc->sym_error_hook = mk_symbol(sc, "*error-hook*");
	sc->sym_sharp_hook = mk_symbol(sc, "*sharp-hook*");
	sc->sym_compile_hook = mk_symbol(sc, "*compile-hook*");

	for(int op=0; op<sizeof(g_dispatch_table)/sizeof(g_dispatch_table[0]); op++) {
		if(g_dispatch_table[op].name!=0) {
			cell_t* sym = mk_symbol(sc, g_dispatch_table[op].name);
			cell_t* proc = mk_proc(sc,(opcode)op);
			new_slot_in_env(sc, sym, proc);
		}
	}
	return 1;
}

void scheme_destroy(scheme *sc) {
	sc->oblist=&g_nil;
	sc->global_env=&g_nil;
	sc->call_stack=&g_nil;
	sc->envir=&g_nil;
	sc->code=&g_nil;
	sc->args=&g_nil;
	sc->ret_value=&g_nil;
	sc->inport=&g_nil;
	sc->outport=&g_nil;
	sc->save_inport=&g_nil;
	sc->loadport=&g_nil;
	gc(sc,&g_nil,&g_nil);

	for(int i=0; i<=sc->last_cell_seg; i++) {
		sc->free(sc->cell_seg[i]);
	}

	for(int i=0; i<=sc->top_file_index; i++) {
		if (sc->load_stack[i].kind & port_file) {
			sc->free(sc->load_stack[i].f.filename);
		}
	}
}

int main(int argc, char **argv) {
	scheme sc;
	if(!scheme_init(&sc,malloc,free)) {
		fprintf(stderr,"Could not initialize!\n");
		return 1;
	}
	FILE* fin=fopen("init.scm","r");
	if(fin!=0) scheme_load_file(&sc,fin,"init.scm");

	if((argc>1) && strcmp(argv[1],"-?")==0) {
		printf("TinyScheme 1.41 修改版(by flysnowxg)\n");
		printf("帮助 :	tinyscheme -?\n");
		printf("启动交互式控制台：tinyscheme\n");
		printf("执行一个文件：tinyscheme  -f <file> [<arg1> <arg2> ...]\n");
		printf("执行一个字符串：tinyscheme  -s command\n");
		return 1;
	}
	else if((argc>1)&& strcmp(argv[1],"-f")){
		char* file_name=argv[1];
		cell_t* args=&g_nil;
		for(argv++;*argv;argv++) {
			cell_t* p=mk_string(&sc,*argv);
			args=cons(&sc,p,args);
		}
		args=reverse(&sc,args);
		scheme_define(&sc,sc.global_env,mk_symbol(&sc,"*args*"),args);
		FILE* fin=fopen(file_name,"r");
		if(fin==0) fprintf(stderr,"Could not open file %s\n",file_name);
		else scheme_load_file(&sc,fin,file_name);
	}
	else if((argc>1)&&(strcmp(argv[1],"-s")==0)){
		scheme_load_string(&sc,argv[1]);
	}
	else{
		printf("TinyScheme 1.41 修改版(by flysnowxg)\n");
		scheme_load_file(&sc,stdin,0);
	}
	scheme_destroy(&sc);
	return sc.eval_result;
}
