# tinyscheme注释  
作者：flysnowxg  
emal:flysnowxg@qq.com  
tinyscheme是一个scheme语言的解释器实现，而这是我大幅修改并加了注释后的tinyscheme（基于tinyscheme1.41）  
原始代码： http://tinyscheme.sourceforge.net/home.html  
tinyscheme据说是实现的r5rs标准（应当是实现了一部分，因为模式匹配和语法定义的那部分显然没实现）  
tinyscheme代码很简短而且实现的语言功能还算比较完整，如果想研究一个lisp解释器的实现，tinyscheme是值得研究的  
tinyscheme实现了lambda、宏、延续、异常、gc这些重要的语言机制，还实现了许多库函数，整个原版代码大约有6500行左右，但是原版代码有很多的宏定义和很多冗余的代码，代码分类也很混乱，可读性不算特别好，在阅读过程中我对这个代码进行了大量的修改，清除了大量冗余代码，重新组织了代码结构，主要的实现文件scheme.c被我从5000行改到只有3400行。所有代码加起来也只有4500行了，功能损失也很小  
并修改一些bug，比如像‘延续’的实现，原版像下面这样的代码中， “(r 1)”这一句是没法运行的  
(define r 0)  
(let ((x 1))  
	(set! x   
		(+ x  
			(call/cc (lambda (c) (set! r c) (+ 44 (c 1)))))  
	)  
	(display x))  
(r 1)  