/*
** $Id: lgc.c $
** Garbage Collector
** See Copyright Notice in lua.h
*/

#define lgc_c
#define LUA_CORE

#include "lprefix.h"

#include <stdio.h>
#include <string.h>


#include "lua.h"

#include "ldebug.h"
#include "ldo.h"
#include "lfunc.h"
#include "lgc.h"
#include "lmem.h"
#include "lobject.h"
#include "lstate.h"
#include "lstring.h"
#include "ltable.h"
#include "ltm.h"


/*
** Maximum number of elements to sweep in each single step.
** (Large enough to dissipate fixed overheads but small enough
** to allow small steps for the collector.)
*/
#define GCSWEEPMAX	100

/*
** Maximum number of finalizers to call in each single step.
*/
#define GCFINMAX	10


/*
** Cost of calling one finalizer.
*/
#define GCFINALIZECOST	50


/*
** The equivalent, in bytes, of one unit of "work" (visiting a slot,
** sweeping an object, etc.)
** x64:16个字节
*/
#define WORK2MEM	sizeof(TValue)


/*
** macro to adjust 'pause': 'pause' is actually used like
** 'pause / PAUSEADJ' (value chosen by tests)
*/
#define PAUSEADJ		100


/* mask with all color bits */
#define maskcolors	(bitmask(BLACKBIT) | WHITEBITS)

/* mask with all GC bits */
#define maskgcbits      (maskcolors | AGEBITS)


/* macro to erase all color bits then set only the current white bit */
#define makewhite(g,x)	\
  (x->marked = cast_byte((x->marked & ~maskcolors) | luaC_white(g)))

/* make an object gray (neither white nor black) */
#define set2gray(x)	resetbits(x->marked, maskcolors)


/* make an object black (coming from any color) */
#define set2black(x)  \
  (x->marked = cast_byte((x->marked & ~WHITEBITS) | bitmask(BLACKBIT)))


#define valiswhite(x)   (iscollectable(x) && iswhite(gcvalue(x)))

#define keyiswhite(n)   (keyiscollectable(n) && iswhite(gckey(n)))


/*
** Protected access to objects in values
*/
#define gcvalueN(o)     (iscollectable(o) ? gcvalue(o) : NULL)

/* 标记对象o的val值为黑色，或者灰色并加入gray中，白色才标记 */
#define markvalue(g,o) { checkliveness(g->mainthread,o); \
  if (valiswhite(o)) reallymarkobject(g,gcvalue(o)); }

/* 标记对象n的key值为黑色，或者灰色并加入gray中 */
#define markkey(g, n)	{ if keyiswhite(n) reallymarkobject(g,gckey(n)); }
/* 标记对象t为黑色，或者灰色并加入gray中 */
#define markobject(g,t)	{ if (iswhite(t)) reallymarkobject(g, obj2gco(t)); }

/*
** mark an object that can be NULL (either because it is really optional,
** or it was stripped as debug info, or inside an uncompleted structure)
** 标记可能为NULL的对象
*/
#define markobjectN(g,t)	{ if (t) markobject(g,t); }

static void reallymarkobject (global_State *g, GCObject *o);
static lu_mem atomic (lua_State *L);
static void entersweep (lua_State *L);

/* cloudwu的gc剖析参考：http://shanks.link/blog/2021/04/09/%E4%BA%91%E9%A3%8E%E7%9A%84blog-lua-gc%E7%9A%84%E6%BA%90%E7%A0%81%E8%A7%A3%E5%89%961/ */
/*
** {======================================================
** Generic functions
** =======================================================
*/


/*
** one after last element in a hash array
*/
#define gnodelast(h)	gnode(h, cast_sizet(sizenode(h)))

/* 根据o的类型，返回gclist字段 */
static GCObject **getgclist (GCObject *o) {
  switch (o->tt) {
    case LUA_VTABLE: return &gco2t(o)->gclist;
    case LUA_VLCL: return &gco2lcl(o)->gclist;
    case LUA_VCCL: return &gco2ccl(o)->gclist;
    case LUA_VTHREAD: return &gco2th(o)->gclist;
    case LUA_VPROTO: return &gco2p(o)->gclist;
    case LUA_VUSERDATA: {
      Udata *u = gco2u(o);
      lua_assert(u->nuvalue > 0);
      return &u->gclist;
    }
    default: lua_assert(0); return 0;
  }
}


/*
** Link a collectable object 'o' with a known type into the list 'p'.
** (Must be a macro to access the 'gclist' field in different types.)
** 把可回收对象O链到P的头部，然后标记O为灰色
*/
#define linkgclist(o,p)	linkgclist_(obj2gco(o), &(o)->gclist, &(p))

static void linkgclist_ (GCObject *o, GCObject **pnext, GCObject **list) {
  lua_assert(!isgray(o));  /* cannot be in a gray list */
  *pnext = *list;
  *list = o;
  set2gray(o);  /* now it is */
}


/*
** Link a generic collectable object 'o' into the list 'p'.
** 把可回收对象O链到P的头部，然后标记O为灰色
*/
#define linkobjgclist(o,p) linkgclist_(obj2gco(o), getgclist(o), &(p))



/*
** Clear keys for empty entries in tables. If entry is empty, mark its
** entry as dead. This allows the collection of the key, but keeps its
** entry in the table: its removal could break a chain and could break
** a table traversal.  Other places never manipulate dead keys, because
** its associated empty value is enough to signal that the entry is
** logically empty.
** 清理表中空value的键。如果一个value是空的，则将其标记为已死亡。这允许回收该键的空间，但仍然保留其在表中的条目
** 移除它可能会打断一个链表，并且可能会影响对表的遍历
** 其他地方从不操作这些已标记为死亡的键，因为与之关联的空值已经足以表明该条目在逻辑上是空的
** Node必须是可回收对象
*/
static void clearkey (Node *n) {
  lua_assert(isempty(gval(n)));
  if (keyiscollectable(n))
    setdeadkey(n);  /* unused key; remove it */
}


/*
** tells whether a key or value can be cleared from a weak
** table. Non-collectable objects are never removed from weak
** tables. Strings behave as 'values', so are never removed too. for
** other objects: if really collected, cannot keep them; for objects
** being finalized, keep them in keys, but not in values
** 判断一个key或者value是否能从弱表里清理掉？
** 非可回收对象是绝对不会从弱表里移除的，字符串作为值来处理，也是绝对不会被移除；
** 对于其他对象：如果确实已经回收，那么就不能保留他们；
** 对于那些正在执行析构的对象，以键的方式保留，而不是值的方式http://lua-users.org/lists/lua-l/2009-03/msg00438.html；
** o是NULL，则为非可回收对象，返回0；
** 字符串直接设为黑色，返回0；
** 通用返回是否是白色；
*/
static int iscleared (global_State *g, const GCObject *o) {
  if (o == NULL) return 0;  /* non-collectable value */
  else if (novariant(o->tt) == LUA_TSTRING) {
    markobject(g, o);  /* strings are 'values', so are never weak */
    return 0;
  }
  else return iswhite(o);
}


/*
** Barrier that moves collector forward, that is, marks the white object
** 'v' being pointed by the black object 'o'.  In the generational
** mode, 'v' must also become old, if 'o' is old; however, it cannot
** be changed directly to OLD, because it may still point to non-old
** objects. So, it is marked as OLD0. In the next cycle it will become
** OLD1, and in the next it will finally become OLD (regular old). By
** then, any object it points to will also be old.  If called in the
** incremental sweep phase, it clears the black object to white (sweep
** it) to avoid other barrier calls for this same object. (That cannot
** be done is generational mode, as its sweep does not distinguish
** whites from deads.)
** GC算法的主要规则：黑色对象不能直接引用白色对象；为啥？因为对象是黑色表示已经被标记过，不会再重新遍历了，那么子对象就没法重新被标记，就会出现新对象被引用但是被释放了；
** 向前屏障，v必须是可回收的白色对象，o必须是黑色；针对sweep清理阶段之前新创建的白色对象被黑色对象所引用；
** gc阶段在<=atomic:直接标记v，v根据类型可以被标为黑色、灰色、或者放入gray链表中等待遍历标记；
** gc阶段在sweep的清理阶段：只针对增量GC模式时，将o标记为当前白色(其实是otherwhite，在atomic最后已经将otherwhite切换为currwhite了，G->currentwhite)
*/
void luaC_barrier_ (lua_State *L, GCObject *o, GCObject *v) {
  global_State *g = G(L);
  lua_assert(isblack(o) && iswhite(v) && !isdead(g, v) && !isdead(g, o));
  if (keepinvariant(g)) {  /* must keep invariant? */
    reallymarkobject(g, v);  /* restore invariant 标记颜色，不希望被清理 */
    if (isold(o)) { /* 分代gc的处理，忽略 */
      lua_assert(!isold(v));  /* white object could not be old */
      setage(v, G_OLD0);  /* restore generational invariant */
    }
  }
  else {  /* sweep phase 如果是在清理阶段，直接设置o为新白色，因为本身清理阶段也是将黑色变为新白色，不会去清理新白色的对象 */
    lua_assert(issweepphase(g));
    if (g->gckind == KGC_INC)  /* incremental mode? */
      makewhite(g, o);  /* mark 'o' as white to avoid other barriers 标记额为白色，减少barrier的开销，后续再有对o的修改也不会触发luaC_barrier_了*/
  }
}


/*
** barrier that moves collector backward, that is, mark the black object
** pointing to a white object as gray again.
** 向后屏障，o必须是黑色，将o设置为灰色并放入grayagain链表中，等待后续遍历
*/
void luaC_barrierback_ (lua_State *L, GCObject *o) {
  global_State *g = G(L);
  lua_assert(isblack(o) && !isdead(g, o));
  lua_assert((g->gckind == KGC_GEN) == (isold(o) && getage(o) != G_TOUCHED1));
  if (getage(o) == G_TOUCHED2)  /* already in gray list? */
    set2gray(o);  /* make it gray to become touched1 */
  else  /* link it in 'grayagain' and paint it gray */
    linkobjgclist(o, g->grayagain);
  if (isold(o))  /* generational mode? */
    setage(o, G_TOUCHED1);  /* touched in current cycle */
}

/*
** 标记o永远不被gc回收：o设为灰色，并从allgc中移除，放到fixedgc链表中
*/
void luaC_fix (lua_State *L, GCObject *o) {
  global_State *g = G(L);
  lua_assert(g->allgc == o);  /* object must be 1st in 'allgc' list! */
  set2gray(o);  /* they will be gray forever */
  setage(o, G_OLD);  /* and old forever */
  g->allgc = o->next;  /* remove object from 'allgc' list */
  o->next = g->fixedgc;  /* link it to 'fixedgc' list */
  g->fixedgc = o;
}


/*
** create a new collectable object (with given type, size, and offset)
** and link it to 'allgc' list.
** 新建可回收对象，并标记为白色，链接到allgc中
** sz一般是结构体大小，例如：sz = sizeof(LX)
** offset一般使用offsetof宏来取结构体字段的偏移大小，例如：offsetof(LX,l)，
** offset的定义：#define offsetof(type, member) ((size_t) &((type *)0)->member)
*/
GCObject *luaC_newobjdt (lua_State *L, int tt, size_t sz, size_t offset) {
  global_State *g = G(L);
  char *p = cast_charp(luaM_newobject(L, novariant(tt), sz));
  GCObject *o = cast(GCObject *, p + offset);
  o->marked = luaC_white(g);
  o->tt = tt;
  o->next = g->allgc;
  g->allgc = o;
  return o;
}

/* 新建可回收对象，并标记为白色，链接到allgc中 */
GCObject *luaC_newobj (lua_State *L, int tt, size_t sz) {
  return luaC_newobjdt(L, tt, sz, 0);
}

/* }====================================================== */



/*
** {======================================================
** Mark functions
** =======================================================
*/


/*
** Mark an object.  Userdata with no user values, strings, and closed
** upvalues are visited and turned black here.  Open upvalues are
** already indirectly linked through their respective threads in the
** 'twups' list, so they don't go to the gray list; nevertheless, they
** are kept gray to avoid barriers, as their values will be revisited
** by the thread or by 'remarkupvals'.  Other objects are added to the
** gray list to be visited (and turned black) later.  Both userdata and
** upvalues can call this function recursively, but this recursion goes
** for at most two levels: An upvalue cannot refer to another upvalue
** (only closures can), and a userdata's metatable must be a table.
** 标记对象颜色为黑色，或者灰色并加入gray中
** 黑色：没有用户值的userdata、字符串、关闭的upvalue；
** 开放的upvalue已经间接地被各自的thread引用在了twups里，所以不加入gray列表，但是也要标记为灰色，避免被屏障，因为他们会被重新访问remarkupvals；
** 其他对象置为灰色并加入gray链表并且在随后的访问的标记为黑色；
** userdata和upvalue可以递归地调用本函数，但最多递归2层：upvalue不会引用另一个upvalue(只有闭包可以),并且userdata的元表必须是table；
*/
static void reallymarkobject (global_State *g, GCObject *o) {
  switch (o->tt) {
    case LUA_VSHRSTR:
    case LUA_VLNGSTR: {
      set2black(o);  /* nothing to visit 字符串一律为黑色*/
      break;
    }
    case LUA_VUPVAL: {
      UpVal *uv = gco2upv(o);
      if (upisopen(uv))
        set2gray(uv);  /* open upvalues are kept gray 开放的upvalue一直都是灰色 */
      else
        set2black(uv);  /* closed upvalues are visited here */
      markvalue(g, uv->v.p);  /* mark its content */
      break;
    }
    case LUA_VUSERDATA: {
      Udata *u = gco2u(o);
      if (u->nuvalue == 0) {  /* no user values? */
        markobjectN(g, u->metatable);  /* mark its metatable */
        set2black(u);  /* nothing else to mark */
        break;
      }
      /* else... */
    }  /* FALLTHROUGH */
    case LUA_VLCL: case LUA_VCCL: case LUA_VTABLE:
    case LUA_VTHREAD: case LUA_VPROTO: {
      linkobjgclist(o, g->gray);  /* to be visited later 只要加入gray的都会标记为灰色*/
      break;
    }
    default: lua_assert(0); break;
  }
}


/*
** mark metamethods for basic types
** 标记所有类型的元方法,设为灰色并直接放入gray中
*/
static void markmt (global_State *g) {
  int i;
  for (i=0; i < LUA_NUMTAGS; i++)
    markobjectN(g, g->mt[i]);
}


/*
** mark all objects in list of being-finalized
** 标记所有正在执行析构的对象，变黑或放入gray中
** 因为这些对象在调用析构函数_gc方法前是不能被回收的，而且它们引用到的其他gc可回收对象，不能在本轮gc中回收，所以需要不断的遍历mark;
*/
static lu_mem markbeingfnz (global_State *g) {
  GCObject *o;
  lu_mem count = 0;
  for (o = g->tobefnz; o != NULL; o = o->next) {
    count++;
    markobject(g, o);
  }
  return count;
}


/*
** For each non-marked thread, simulates a barrier between each open
** upvalue and its value. (If the thread is collected, the value will be
** assigned to the upvalue, but then it can be too late for the barrier
** to act. The "barrier" does not need to check colors: A non-marked
** thread must be young; upvalues cannot be older than their threads; so
** any visited upvalue must be young too.) Also removes the thread from
** the list, as it was already visited. Removes also threads with no
** upvalues, as they have nothing to be checked. (If the thread gets an
** upvalue later, it will be linked in the list again.)
** 重新标记协程的开放upavlues;
** 对每个没有标记过的thread，也就是白色的，没有被引用的dead状态，对它里面的upvalue和指向的值模拟一个屏障；
** 如果协程被回收了，upvalue的值会指向它自己的value，但那时候做屏障已经太迟了；
** 同时把thread从twup里移除，因为已经访问过了，没有upvalues的thread也移除，因为它没有upvalue来做检查了，但如果它后续新增了upvalue，会被重新加入twup里；
** 如何理解这里：有open upvalue的thread会放到twups里，但是访问的时候可能thread已经dead了，所以是白色，但如果它还有openupvalue呢？比如：在这个协程里
** 定义了一个有openupvalue的函数，并在全局变量里引用了这个函数，那么这个函数会被访问并标记，同时他的upvalues也会被标记，但因为openupvalue是指向thread的栈里
** 的对象，那么有可能在遍历后函数的upvalue变化了，比如local a = "xx";f被遍历标记；然后a在其他函数里被修改为a={},那么这个a需要被重新标记不能被回收。
** 另外参考：https://www.cnblogs.com/lindx/p/17590730.html
*/
static int remarkupvals (global_State *g) {
  lua_State *thread;
  /* 加到twup里的都是有openupval的thread，但是thread有可能已经执行结束被设置为了nil，没有地方在引用它了、或者它里面的函数调用结束了，upvalue都被删除了 */
  lua_State **p = &g->twups; 
  int work = 0;  /* estimate of how much work was done here */
  while ((thread = *p) != NULL) {
    work++;
    if (!iswhite(thread) && thread->openupval != NULL)
      p = &thread->twups;  /* keep marked thread with upvalues in the list */
    else {  /* thread is not marked or without upvalues */
      UpVal *uv;
      lua_assert(!isold(thread) || thread->openupval == NULL);
      *p = thread->twups;  /* remove thread from the list */
      thread->twups = thread;  /* mark that it is out of list 将twups指向自己来表示已从g里删除*/
      for (uv = thread->openupval; uv != NULL; uv = uv->u.open.next) {
        lua_assert(getage(uv) <= getage(thread));
        work++;
        if (!iswhite(uv)) {  /* upvalue already visited? upvalue已经被访问过了 */
          lua_assert(upisopen(uv) && isgray(uv));
          markvalue(g, uv->v.p);  /* mark its value 标记upvalue里指向的对象，开放的upvalue都是在栈上 */
        }
      }
    }
  }
  return work;
}

/*
** 重置所有gray和weaks的list为NULL
*/
static void cleargraylists (global_State *g) {
  g->gray = g->grayagain = NULL;
  g->weak = g->allweak = g->ephemeron = NULL;
}


/*
** mark root set and reset all gray lists, to start a new collection
** 开始新一轮回收
** 1、重置所有gray和weaks的list为NULL
** 2、标记全局的mainthread、l_registry、mt
** 3、标记正在析构的userdata,在g->tobefnz
*/
static void restartcollection (global_State *g) {
  cleargraylists(g);
  markobject(g, g->mainthread);
  markvalue(g, &g->l_registry);
  markmt(g);
  markbeingfnz(g);  /* mark any finalizing object left from previous cycle */
}

/* }====================================================== */


/*
** {======================================================
** Traverse functions
** =======================================================
*/


/*
** Check whether object 'o' should be kept in the 'grayagain' list for
** post-processing by 'correctgraylist'. (It could put all old objects
** in the list and leave all the work to 'correctgraylist', but it is
** more efficient to avoid adding elements that will be removed.) Only
** TOUCHED1 objects need to be in the list. TOUCHED2 doesn't need to go
** back to a gray list, but then it must become OLD. (That is what
** 'correctgraylist' does when it finds a TOUCHED2 object.)
** 分代的，可以暂时忽略
*/
static void genlink (global_State *g, GCObject *o) {
  lua_assert(isblack(o));
  if (getage(o) == G_TOUCHED1) {  /* touched in this cycle? */
    linkobjgclist(o, g->grayagain);  /* link it back in 'grayagain' */
  }  /* everything else do not need to be linked back */
  else if (getage(o) == G_TOUCHED2)
    changeage(o, G_TOUCHED2, G_OLD);  /* advance age */
}


/*
** Traverse a table with weak values and link it to proper list. During
** propagate phase, keep it in 'grayagain' list, to be revisited in the
** atomic phase. In the atomic phase, if table has any white value,
** put it in 'weak' list, to be cleared.
** h已被标记为黑色，遍历标记弱值表
** 1、表中：值为空则设为deadkey，后续会被直接释放；值不为空，标记key为黑色，或者灰色并加入gray
** 2、表中数组部分不标记，因为会加入weak或者grayagain，在atomic阶段遍历
** 3、如果在传播阶段，直接放入grayagain，在atomic阶段一起遍历
** 4、如果在atomic阶段并且(数组只要有值或者有白色的value)，就放入weak链表，在atomic阶段一起遍历
*/
static void traverseweakvalue (global_State *g, Table *h) {
  Node *n, *limit = gnodelast(h);
  /* if there is array part, assume it may have white values (it is not
     worth traversing it now just to check) */
  int hasclears = (h->alimit > 0);  /* 因为是弱值，如果都没有被引用，那么都应该清理，所以数组不遍历，反正后续还会遍历 */
  for (n = gnode(h, 0); n < limit; n++) {  /* traverse hash part */
    if (isempty(gval(n)))  /* entry is empty? */
      clearkey(n);  /* clear its key 值是空，可以清理，标记deadkey*/
    else {
      lua_assert(!keyisnil(n));
      markkey(g, n);  /* 只标记key,不主动标记弱值，key是否释放，根据最后的状态：是deadkey或者value是白色 */
      if (!hasclears && iscleared(g, gcvalueN(gval(n))))  /* a white value? */
        hasclears = 1;  /* table will have to be cleared */
    }
  }
  if (g->gcstate == GCSatomic && hasclears)
    linkgclist(h, g->weak);  /* has to be cleared later 改成灰色，放入弱值链表里 */
  else
    linkgclist(h, g->grayagain);  /* must retraverse it in atomic phase 改成灰色，放入grayagin链表里 */
}


/*
** Traverse an ephemeron table and link it to proper list. Returns true
** iff any object was marked during this traversal (which implies that
** convergence has to continue). During propagation phase, keep table
** in 'grayagain' list, to be visited again in the atomic phase. In
** the atomic phase, if table has any white->white entry, it has to
** be revisited during ephemeron convergence (as that key may turn
** black). Otherwise, if it has any white key, table has to be cleared
** (in the atomic phase). In generational mode, some tables
** must be kept in some gray list for post-processing; this is done
** by 'genlink'.
** h已被标记为黑色，遍历标记弱key表，返回是否有字段被标记过
** 1、遍历标记数组部分，因为值是强引用，需要遍历，key对应数组的下标没有对象；
** 2、表中：
**    值为空则设为deadkey，后续会被直接释放；
**    key被标记了的，值也执行标记为黑色，或者灰色放入gray中；
**    key-value没被标记的，不做处理；
**    key没被标记，值标记了，不做处理；
** 3、放入哪个链表？
**    传播阶段，放入grayagain中；
**    只要有key-value都是白色，表变灰并放入ephemeron链表中，这里的白色不是真的就会释放的，它可能在后续的遍历中被改变；
**    有白色的key，放入allweak中；
*/
static int traverseephemeron (global_State *g, Table *h, int inv) {
  int marked = 0;  /* true if an object is marked in this traversal 代表表里有没有值被标记过 */
  int hasclears = 0;  /* true if table has white keys */
  int hasww = 0;  /* true if table has entry "white-key -> white-value" */
  unsigned int i;
  unsigned int asize = luaH_realasize(h);
  unsigned int nsize = sizenode(h);
  /* traverse array part 标记数组的值为黑色、或者灰色并加入gray中 */
  for (i = 0; i < asize; i++) {
    if (valiswhite(&h->array[i])) {
      marked = 1;
      reallymarkobject(g, gcvalue(&h->array[i]));
    }
  }
  /* traverse hash part; if 'inv', traverse descending
     (see 'convergeephemerons') */
  for (i = 0; i < nsize; i++) {
    Node *n = inv ? gnode(h, nsize - 1 - i) : gnode(h, i);
    if (isempty(gval(n)))  /* entry is empty? */
      clearkey(n);  /* clear its key 值是空的，标记为deadkey */
    else if (iscleared(g, gckeyN(n))) {  /* key is not marked (yet)? 这里key还是白色，有2种情况：都遍历完了没有被引用、还没遍历到它*/
      hasclears = 1;  /* table must be cleared */
      if (valiswhite(gval(n)))  /* value not marked yet? 值也是白色，key-value都是白色时放入瞬表里*/
        hasww = 1;  /* white-white entry */
    }
    else if (valiswhite(gval(n))) {  /* value not marked yet? 如果key被访问到标记了，说明key的对象被引用着，那么值也应该不能被释放*/
      marked = 1;
      reallymarkobject(g, gcvalue(gval(n)));  /* mark it now 值没有标记，那就标记颜色避免被清理*/
    }
  }
  /* link table into proper list */
  if (g->gcstate == GCSpropagate)
    linkgclist(h, g->grayagain);  /* must retraverse it in atomic phase 传播阶段，变灰并放入grayagain中，在atomic中再遍历一次 */
  else if (hasww)  /* table has white->white entries? */
    linkgclist(h, g->ephemeron);  /* have to propagate again 有白色的key-value，变灰并放入瞬表，在atomic中再遍历一次 */
  else if (hasclears)  /* table has white keys? 有白色的key，并且value被引用着，可能需要被清理*/
    linkgclist(h, g->allweak);  /* may have to clean white keys 变灰并放入allweak中，在atomic中再遍历一次 */
  else
    genlink(g, obj2gco(h));  /* check whether collector still needs to see it */
  return marked;
}

/* 
** h已经是黑色，遍历标记表h里所有引用的对象
** h是强表，表示key和value都是强引用，遍历到h就要标记里面所有的内容
** 1、标记所有数组里的值为黑色或者置灰并放入gray中
** 2、标记所有hash里的值为黑色或者置灰并放入gray中、如果value为null，则标记为deadkey
*/
static void traversestrongtable (global_State *g, Table *h) {
  Node *n, *limit = gnodelast(h);
  unsigned int i;
  unsigned int asize = luaH_realasize(h);
  for (i = 0; i < asize; i++)  /* traverse array part 标记数组内所有对象为黑色或者置灰并放入gray中 */
    markvalue(g, &h->array[i]);
  for (n = gnode(h, 0); n < limit; n++) {  /* traverse hash part */
    if (isempty(gval(n)))  /* entry is empty? */
      clearkey(n);  /* clear its key 标记空的key为dead，等清理阶段释放*/
    else {
      lua_assert(!keyisnil(n));
      markkey(g, n); /* 标记key为黑色或者置灰并放入gray中 */
      markvalue(g, gval(n));  /* 标记value为黑色或者置灰并放入gray中 */
    }
  }
  genlink(g, obj2gco(h));
}

/*
** h已经是黑色，遍历标记表h引用的所有对象
** 1、根据表的类型进行不同处理
** 2、弱表有3种，会分别置灰放入不同的链表：弱key表->ephemeron、弱值表->weak、弱kv表-allweak，也可能放入grayagain中
*/
static lu_mem traversetable (global_State *g, Table *h) {
  const char *weakkey, *weakvalue;
  const TValue *mode = gfasttm(g, h->metatable, TM_MODE); /* 获取弱表模式 */
  TString *smode;
  markobjectN(g, h->metatable); /* 标记元表及其引用对象,放进gray，下一次最先遍历 */
  if (mode && ttisshrstring(mode) &&  /* is there a weak mode? */
      (cast_void(smode = tsvalue(mode)),
       cast_void(weakkey = strchr(getshrstr(smode), 'k')),
       cast_void(weakvalue = strchr(getshrstr(smode), 'v')),
       (weakkey || weakvalue))) {  /* is really weak? */
    if (!weakkey)  /* strong keys? 是k强v弱的weak表 */
      traverseweakvalue(g, h);
    else if (!weakvalue)  /* strong values? 是k弱v强的ephemeron瞬表*/
      traverseephemeron(g, h, 0);
    else  /* all weak 是kv都弱的allweak表 */
      linkgclist(h, g->allweak);  /* nothing to traverse now 把h变灰，放入allweak链表，等待atomic阶段遍历*/
  }
  else  /* not weak 是kv都强引用的表 */
    traversestrongtable(g, h); /* 强表的key和value都会被标记为黑色、或者灰色并加入gray中 */
  return 1 + h->alimit + 2 * allocsizenode(h);
}

/*
** u是黑色，遍历标记u引用的对象
** 1、标记metatable
** 2、标记所有的userdata值
*/
static int traverseudata (global_State *g, Udata *u) {
  int i;
  markobjectN(g, u->metatable);  /* mark its metatable */
  for (i = 0; i < u->nuvalue; i++)
    markvalue(g, &u->uv[i].uv);
  genlink(g, obj2gco(u));
  return 1 + u->nuvalue;
}


/*
** Traverse a prototype. (While a prototype is being build, its
** arrays can be larger than needed; the extra slots are filled with
** NULL, so the use of 'markobjectN')
** 标记函数原型里的对象，f为黑色
** 1、标记source源码文件字符
** 2、标记upvalue的名字字符
** 3、标记嵌套的函数proto，标灰放入gray链表
** 4、标记所有局部变量的名字字符
*/
static int traverseproto (global_State *g, Proto *f) {
  int i;
  markobjectN(g, f->source);
  for (i = 0; i < f->sizek; i++)  /* mark literals */
    markvalue(g, &f->k[i]);
  for (i = 0; i < f->sizeupvalues; i++)  /* mark upvalue names */
    markobjectN(g, f->upvalues[i].name);
  for (i = 0; i < f->sizep; i++)  /* mark nested protos */
    markobjectN(g, f->p[i]);
  for (i = 0; i < f->sizelocvars; i++)  /* mark local-variable names */
    markobjectN(g, f->locvars[i].varname);
  return 1 + f->sizek + f->sizeupvalues + f->sizep + f->sizelocvars;
}

/*
** 标记C闭包里的对象，cl为黑色
** 1、标记所有的UpVals，可能为黑色或者灰色，同时标记upval里存的值
*/
static int traverseCclosure (global_State *g, CClosure *cl) {
  int i;
  for (i = 0; i < cl->nupvalues; i++)  /* mark its upvalues */
    markvalue(g, &cl->upvalue[i]);
  return 1 + cl->nupvalues;
}

/*
** Traverse a Lua closure, marking its prototype and its upvalues.
** (Both can be NULL while closure is being created.)
** 标记Lua闭包里的对象，cl为黑色
** 1、标记Proto为灰色，并加入gray链表
** 2、标记所有的UpVals，可能为黑色或者灰色，同时标记upval里存的值
** 3、Proto和upval都可能为null，如果闭包正在被创建中，为什么会出现这种情况？
**  因为：LClosure可能会逐步构建，初始new出来的时候，p和upvals都为NULL，后续逐步构建内容
*/
static int traverseLclosure (global_State *g, LClosure *cl) {
  int i;
  markobjectN(g, cl->p);  /* mark its prototype */
  for (i = 0; i < cl->nupvalues; i++) {  /* visit its upvalues */
    UpVal *uv = cl->upvals[i];
    markobjectN(g, uv);  /* mark upvalue */
  }
  return 1 + cl->nupvalues;
}


/*
** Traverse a thread, marking the elements in the stack up to its top
** and cleaning the rest of the stack in the final traversal. That
** ensures that the entire stack have valid (non-dead) objects.
** Threads have no barriers. In gen. mode, old threads must be visited
** at every cycle, because they might point to young objects.  In inc.
** mode, the thread can still be modified before the end of the cycle,
** and therefore it must be visited again in the atomic phase. To ensure
** these visits, threads must return to a gray list if they are not new
** (which can only happen in generational mode) or if the traverse is in
** the propagate phase (which can only happen in incremental mode).
** 遍历标记thread类型的luaState，th为黑色
** 1、如果stack还没初始化完成，不处理
** 2、标记栈里的所有对象
** 3、如果有开放的upvalue，标记所有的upvalue
** 4、分阶段的处理：
**    传播阶段：直接放入grayagain里，因为在传播阶段后续可能还会被修改，而stack上数据的修改是不经过write barrier的。也没有必要为最频繁的stack修改做barrier那样对性能影响就很大。
**    atomic阶段：收缩stack，并且把top以后的都清空；有开放的upvalue但没有在g->twups中，放到twups中
*/
static int traversethread (global_State *g, lua_State *th) {
  UpVal *uv;
  StkId o = th->stack.p;
  if (isold(th) || g->gcstate == GCSpropagate)
    linkgclist(th, g->grayagain);  /* insert into 'grayagain' list 标灰放入grayagain等atomic阶段再遍历一次 */
  if (o == NULL)
    return 1;  /* stack not completely built yet */
  lua_assert(g->gcstate == GCSatomic ||
             th->openupval == NULL || isintwups(th));
  for (; o < th->top.p; o++)  /* mark live elements in the stack 标记栈里的对象*/
    markvalue(g, s2v(o));
  for (uv = th->openupval; uv != NULL; uv = uv->u.open.next)
    markobject(g, uv);  /* open upvalues cannot be collected 标记开放的upvalues*/
  if (g->gcstate == GCSatomic) {  /* final traversal? */
    if (!g->gcemergency)
      luaD_shrinkstack(th); /* do not change stack in emergency cycle */
    for (o = th->top.p; o < th->stack_last.p + EXTRA_STACK; o++)
      setnilvalue(s2v(o));  /* clear dead stack slice 清理栈中未使用的部分 */
    /* 'remarkupvals' may have removed thread from 'twups' list */
    if (!isintwups(th) && th->openupval != NULL) {
      th->twups = g->twups;  /* link it back to the list 有开放的upvalue但没有在g->twups中，放进去,同时thread也是存活的*/
      g->twups = th;
    }
  }
  return 1 + stacksize(th);
}


/*
** traverse one gray object, turning it to black.
** 从g->gray中每次取出一个对象o，
** 1、标记o为黑色,从gray里移除
** 2、遍历标记o关联的所有对象，使用广度遍历
*/
static lu_mem propagatemark (global_State *g) {
  GCObject *o = g->gray;
  nw2black(o);
  g->gray = *getgclist(o);  /* remove from 'gray' list */
  switch (o->tt) {
    case LUA_VTABLE: return traversetable(g, gco2t(o));
    case LUA_VUSERDATA: return traverseudata(g, gco2u(o));
    case LUA_VLCL: return traverseLclosure(g, gco2lcl(o));
    case LUA_VCCL: return traverseCclosure(g, gco2ccl(o));
    case LUA_VPROTO: return traverseproto(g, gco2p(o));
    case LUA_VTHREAD: return traversethread(g, gco2th(o));
    default: lua_assert(0); return 0;
  }
}


static lu_mem propagateall (global_State *g) {
  lu_mem tot = 0;
  while (g->gray)
    tot += propagatemark(g);
  return tot;
}


/*
** Traverse all ephemeron tables propagating marks from keys to values.
** Repeat until it converges, that is, nothing new is marked. 'dir'
** inverts the direction of the traversals, trying to speed up
** convergence on chains in the same table.
** 遍历标记所有的瞬表，直到收敛，收敛的意思是所有的瞬表里都没有进行过标记操作了；
** 因为瞬表是弱key表，它的值可能会被当做key，当该值被标记了，那么它作为key对应的value也要被标记；
** 循环结束后的情况：
** 1、g->ephemeron：里面可能还有瞬表，这些瞬表有key-value都是白色的entry，但已经没有什么标记的了；
** 2、g->allweak：大部分在这里面，有白色的key的瞬表会放进去，但所有白色的key对应的value都已被标记过了，不然的话就是在g->ephemeron里；
*/
static void convergeephemerons (global_State *g) {
  int changed;
  int dir = 0;
  do {
    GCObject *w;
    GCObject *next = g->ephemeron;  /* get ephemeron list */
    g->ephemeron = NULL;  /* tables may return to this list when traversed */
    changed = 0;
    while ((w = next) != NULL) {  /* for each ephemeron table */
      Table *h = gco2t(w);
      next = h->gclist;  /* list is rebuilt during loop */
      nw2black(h);  /* out of the list (for now) 从灰色变为黑色，并从list中移除，避免重复标记，但它有可能在还会被放入ephemeron被继续遍历 */
      if (traverseephemeron(g, h, dir)) {  /* marked some value? 有值被标记，有可能放入了gray链表中，继续清空gray */
        propagateall(g);  /* propagate changes */
        changed = 1;  /* will have to revisit all ephemeron tables 只要有一个瞬表有变化，那么就要重新遍历所有的瞬表 */
      }
    }
    dir = !dir;  /* invert direction next time */
  } while (changed);  /* repeat until no more changes */
}

/* }====================================================== */


/*
** {======================================================
** Sweep Functions
** =======================================================
*/


/*
** clear entries with unmarked keys from all weaktables in list 'l'
** 遍历清理弱表里面key没有被标记的所有entry；
** 1、key没有被标记，设置value为empty；
** 2、value如果为empty，标记key为deadkey；
*/
static void clearbykeys (global_State *g, GCObject *l) {
  for (; l; l = gco2t(l)->gclist) {
    Table *h = gco2t(l);
    Node *limit = gnodelast(h);
    Node *n;
    for (n = gnode(h, 0); n < limit; n++) {
      if (iscleared(g, gckeyN(n)))  /* unmarked key? */
        setempty(gval(n));  /* remove entry */
      if (isempty(gval(n)))  /* is entry empty? */
        clearkey(n);  /* clear its key */
    }
  }
}


/*
** clear entries with unmarked values from all weaktables in list 'l' up
** to element 'f'
** 清理链表中所有没有被标记过的value，以及对应的key,没被标记过是指从gcroot遍历不到它，需要释放内存；
** 数组部分：value没有被引用，直接设置为empty；
** 哈希部分：value没有标记过，设置为empty，同时把key标记为deadkey；
*/
static void clearbyvalues (global_State *g, GCObject *l, GCObject *f) {
  for (; l != f; l = gco2t(l)->gclist) {
    Table *h = gco2t(l);
    Node *n, *limit = gnodelast(h);
    unsigned int i;
    unsigned int asize = luaH_realasize(h);
    for (i = 0; i < asize; i++) {
      TValue *o = &h->array[i];
      if (iscleared(g, gcvalueN(o)))  /* value was collected? */
        setempty(o);  /* remove entry */
    }
    for (n = gnode(h, 0); n < limit; n++) {
      if (iscleared(g, gcvalueN(gval(n))))  /* unmarked value? */
        setempty(gval(n));  /* remove entry */
      if (isempty(gval(n)))  /* is entry empty? */
        clearkey(n);  /* clear its key */
    }
  }
}

/* 释放upvalue的内存，如果是开放的upvalue，从openupvalue的链表中删除 */
static void freeupval (lua_State *L, UpVal *uv) {
  if (upisopen(uv))
    luaF_unlinkupval(uv);
  luaM_free(L, uv);
}

/* 根据对象o的类型执行具体内存释放 */
static void freeobj (lua_State *L, GCObject *o) {
  switch (o->tt) {
    case LUA_VPROTO:
      luaF_freeproto(L, gco2p(o));
      break;
    case LUA_VUPVAL:
      freeupval(L, gco2upv(o));
      break;
    case LUA_VLCL: {
      LClosure *cl = gco2lcl(o);
      luaM_freemem(L, cl, sizeLclosure(cl->nupvalues));
      break;
    }
    case LUA_VCCL: {
      CClosure *cl = gco2ccl(o);
      luaM_freemem(L, cl, sizeCclosure(cl->nupvalues));
      break;
    }
    case LUA_VTABLE:
      luaH_free(L, gco2t(o));
      break;
    case LUA_VTHREAD:
      luaE_freethread(L, gco2th(o));
      break;
    case LUA_VUSERDATA: {
      Udata *u = gco2u(o);
      luaM_freemem(L, o, sizeudata(u->nuvalue, u->len));
      break;
    }
    case LUA_VSHRSTR: {
      TString *ts = gco2ts(o);
      luaS_remove(L, ts);  /* remove it from hash table */
      luaM_freemem(L, ts, sizelstring(ts->shrlen));
      break;
    }
    case LUA_VLNGSTR: {
      TString *ts = gco2ts(o);
      luaM_freemem(L, ts, sizelstring(ts->u.lnglen));
      break;
    }
    default: lua_assert(0);
  }
}


/*
** sweep at most 'countin' elements from a list of GCObjects erasing dead
** objects, where a dead object is one marked with the old (non current)
** white; change all non-dead objects back to white, preparing for next
** collection cycle. Return where to continue the traversal or NULL if
** list is finished. ('*countout' gets the number of elements traversed.)
** 遍历释放链表里的白色对象，遍历countin次，返回countout个处理的对象个数
** 返回值:下次需要访问的对象的next字段地址
*/
static GCObject **sweeplist (lua_State *L, GCObject **p, int countin,
                             int *countout) {
  global_State *g = G(L);
  int ow = otherwhite(g);
  int i;
  int white = luaC_white(g);  /* current white */
  for (i = 0; *p != NULL && i < countin; i++) {
    GCObject *curr = *p;
    int marked = curr->marked;
    if (isdeadm(ow, marked)) {  /* is 'curr' dead? 是之前的白色，说明没有引用了 */
      *p = curr->next;  /* remove 'curr' from list 要释放的对象，把p指针里的内容设置为next，p的地址不会变 */
      freeobj(L, curr);  /* erase 'curr' */
    }
    else {  /* change mark to 'white' */
      curr->marked = cast_byte((marked & ~maskgcbits) | white); /* 设置新白色的标记 */
      p = &curr->next;  /* go to next element 跳到下一个对象是通过p指向next的地址，p的地址会变 */
    }
  }
  if (countout)
    *countout = i;  /* number of elements traversed */
  return (*p == NULL) ? NULL : p;
}


/*
** sweep a list until a live object (or end of list)
** 顺序清理链表，直到遇到存活的对象
*/
static GCObject **sweeptolive (lua_State *L, GCObject **p) {
  GCObject **old = p;
  do {
    p = sweeplist(L, p, 1, NULL);
  /* 因为每次都是从头部遍历一个对象，如果是清理，是把p指向的内容设置为了下一个，那么old的内容和p就是一样的；
  如果是存活对象则会跳过，会修改p指向下一个指针的地址，这时候old和p就不同了*/
  } while (p == old); /* 如果一直没有遇到存活的对象，继续释放一个 */
  return p;
}

/* }====================================================== */


/*
** {======================================================
** Finalization
** =======================================================
*/

/*
** If possible, shrink string table.
** 检查strt缓存表的大小，如果空余太多，进行缩容
*/
static void checkSizes (lua_State *L, global_State *g) {
  if (!g->gcemergency) {
    if (g->strt.nuse < g->strt.size / 4) {  /* string table too big? */
      l_mem olddebt = g->GCdebt;
      luaS_resize(L, g->strt.size / 2);
      g->GCestimate += g->GCdebt - olddebt;  /* correct estimate */
    }
  }
}


/*
** Get the next udata to be finalized from the 'tobefnz' list, and
** link it back into the 'allgc' list.
** 从tobefnz链表里获取一个对象：从tobefnz里移除、放回allgc中、如果在清理阶段就标记为白色
** tobefnz里的对象，在这次gc中只调用析构函数，不会释放，下一次gc才释放
*/
static GCObject *udata2finalize (global_State *g) {
  GCObject *o = g->tobefnz;  /* get first element */
  lua_assert(tofinalize(o));
  g->tobefnz = o->next;  /* remove it from 'tobefnz' list */
  o->next = g->allgc;  /* return it to 'allgc' list 下次gc再释放对象 */
  g->allgc = o;
  resetbit(o->marked, FINALIZEDBIT);  /* object is "normal" again */
  if (issweepphase(g))
    makewhite(g, o);  /* "sweep" object */
  else if (getage(o) == G_OLD1)
    g->firstold1 = o;  /* it is the first OLD1 object in the list */
  return o;
}

/* 调用析构函数_gc, 不允许在调用链中有yield调用,2个参数，没有返回值 */
static void dothecall (lua_State *L, void *ud) {
  UNUSED(ud);
  luaD_callnoyield(L, L->top.p - 2, 0);
}

/* 从tobefnz获取对象，并pcall析构函数_gc
** 调用前要保存些状态用于恢复
*/
static void GCTM (lua_State *L) {
  global_State *g = G(L);
  const TValue *tm;
  TValue v;
  lua_assert(!g->gcemergency);
  setgcovalue(L, &v, udata2finalize(g)); /* 获取对象并保存在v里 */
  tm = luaT_gettmbyobj(L, &v, TM_GC); /* 获取_gc元方法 */
  if (!notm(tm)) {  /* is there a finalizer? */
    int status;
    lu_byte oldah = L->allowhook;
    int oldgcstp  = g->gcstp;
    g->gcstp |= GCSTPGC;  /* avoid GC steps */
    L->allowhook = 0;  /* stop debug hooks during GC metamethod */
    setobj2s(L, L->top.p++, tm);  /* push finalizer... */
    setobj2s(L, L->top.p++, &v);  /* ... and its argument 参数是它自己 */
    L->ci->callstatus |= CIST_FIN;  /* will run a finalizer */
    status = luaD_pcall(L, dothecall, NULL, savestack(L, L->top.p - 2), 0);
    L->ci->callstatus &= ~CIST_FIN;  /* not running a finalizer anymore */
    L->allowhook = oldah;  /* restore hooks */
    g->gcstp = oldgcstp;  /* restore state */
    if (l_unlikely(status != LUA_OK)) {  /* error while running __gc? */
      luaE_warnerror(L, "__gc");
      L->top.p--;  /* pops error object */
    }
  }
}


/*
** Call a few finalizers
** 最多n个对象析构
*/
static int runafewfinalizers (lua_State *L, int n) {
  global_State *g = G(L);
  int i;
  for (i = 0; i < n && g->tobefnz; i++)
    GCTM(L);  /* call one finalizer */
  return i;
}


/*
** call all pending finalizers 调用所有对象的析构函数
*/
static void callallpendingfinalizers (lua_State *L) {
  global_State *g = G(L);
  while (g->tobefnz)
    GCTM(L);
}


/*
** find last 'next' field in list 'p' list (to add elements in its end)
** 查找p所在链表的最后一个对象的next字段地址，并返回指向next地址的指针
*/
static GCObject **findlast (GCObject **p) {
  while (*p != NULL)
    p = &(*p)->next;
  return p;
}


/*
** Move all unreachable objects (or 'all' objects) that need
** finalization from list 'finobj' to list 'tobefnz' (to be finalized).
** (Note that objects after 'finobjold1' cannot be white, so they
** don't need to be traversed. In incremental mode, 'finobjold1' is NULL,
** so the whole list is traversed.)
** 把所有带有析构函数的可回收对象从finobj链表中移到tobefnz上，成为即将调用析构函数的对象
*/
static void separatetobefnz (global_State *g, int all) {
  GCObject *curr;
  GCObject **p = &g->finobj;
  GCObject **lastnext = findlast(&g->tobefnz);
  while ((curr = *p) != g->finobjold1) {  /* traverse all finalizable objects */
    lua_assert(tofinalize(curr));
    if (!(iswhite(curr) || all))  /* not being collected? 还引用着就表示还在使用，不需要处理 */
      p = &curr->next;  /* don't bother with it */
    else {
      if (curr == g->finobjsur)  /* removing 'finobjsur'? */
        g->finobjsur = curr->next;  /* correct it */
      *p = curr->next;  /* remove 'curr' from 'finobj' list */
      curr->next = *lastnext;  /* link at the end of 'tobefnz' list */
      *lastnext = curr;
      lastnext = &curr->next;
    }
  }
}


/*
** If pointer 'p' points to 'o', move it to the next element.
** 分代-忽略
*/
static void checkpointer (GCObject **p, GCObject *o) {
  if (o == *p)
    *p = o->next;
}


/*
** Correct pointers to objects inside 'allgc' list when
** object 'o' is being removed from the list.
** 分代-忽略
*/
static void correctpointers (global_State *g, GCObject *o) {
  checkpointer(&g->survival, o);
  checkpointer(&g->old1, o);
  checkpointer(&g->reallyold, o);
  checkpointer(&g->firstold1, o);
}


/*
** if object 'o' has a finalizer, remove it from 'allgc' list (must
** search the list to find it) and link it in 'finobj' list.
** 如果o有析构函数，那么从allgc里移除，加到finobj中；
** 在allgc中查找有消耗：最好一开始就把所有对象的析构函数设置好，不要动态添加；
*/
void luaC_checkfinalizer (lua_State *L, GCObject *o, Table *mt) {
  global_State *g = G(L);
  if (tofinalize(o) ||                 /* obj. is already marked... */
      gfasttm(g, mt, TM_GC) == NULL ||    /* or has no finalizer... */
      (g->gcstp & GCSTPCLS))                   /* or closing state? */
    return;  /* nothing to be done */
  else {  /* move 'o' to 'finobj' list */
    GCObject **p;
    if (issweepphase(g)) {
      makewhite(g, o);  /* "sweep" object 'o' 如果是在清理阶段，标记为新白色不被清理 */
      if (g->sweepgc == &o->next)  /* should not remove 'sweepgc' object 如果当前的sweepgc正指向o，跳过o，让它指向后面的存活对象 */
        g->sweepgc = sweeptolive(L, g->sweepgc);  /* change 'sweepgc' */
    }
    else
      correctpointers(g, o);
    /* search for pointer pointing to 'o' 这里要在allgc里查找，消耗挺大，所以最好一开始就把所有对象的析构函数设置好，不要动态添加 */
    for (p = &g->allgc; *p != o; p = &(*p)->next) { /* empty */ }
    *p = o->next;  /* remove 'o' from 'allgc' list 从allgc里删除 */
    o->next = g->finobj;  /* link it in 'finobj' list 加到finobj中，头部 */
    g->finobj = o;
    l_setbit(o->marked, FINALIZEDBIT);  /* mark it as such 标记有析构函数 */
  }
}

/* }====================================================== */


/*
** {======================================================
** Generational Collector
** =======================================================
*/


/*
** Set the "time" to wait before starting a new GC cycle; cycle will
** start when memory use hits the threshold of ('estimate' * pause /
** PAUSEADJ). (Division by 'estimate' should be OK: it cannot be zero,
** because Lua cannot even start with less than PAUSEADJ bytes).
** 根据一次gc后，当前所有对象的总内存来计算下一次gc触发的debt内存量；
** gcpause默认是200，threshold下一次gc触发的预算总内存
*/
static void setpause (global_State *g) {
  l_mem threshold, debt;
  int pause = getgcparam(g->gcpause);
  l_mem estimate = g->GCestimate / PAUSEADJ;  /* adjust 'estimate' 为了和gcpause参数一致的倍数 */
  lua_assert(estimate > 0);
  threshold = (pause < MAX_LMEM / estimate)  /* overflow? */
            ? estimate * pause  /* no overflow */
            : MAX_LMEM;  /* overflow; truncate to maximum */
  debt = gettotalbytes(g) - threshold;
  if (debt > 0) debt = 0; /* 如果大于0，强制设置为0，避免下一帧马上又执行gcstep，等到有新内存申请时才触发 */
  luaE_setdebt(g, debt);
}


/*
** Sweep a list of objects to enter generational mode.  Deletes dead
** objects and turns the non dead to old. All non-dead threads---which
** are now old---must be in a gray list. Everything else is not in a
** gray list. Open upvalues are also kept gray.
** 分代-忽略
*/
static void sweep2old (lua_State *L, GCObject **p) {
  GCObject *curr;
  global_State *g = G(L);
  while ((curr = *p) != NULL) {
    if (iswhite(curr)) {  /* is 'curr' dead? */
      lua_assert(isdead(g, curr));
      *p = curr->next;  /* remove 'curr' from list */
      freeobj(L, curr);  /* erase 'curr' */
    }
    else {  /* all surviving objects become old */
      setage(curr, G_OLD);
      if (curr->tt == LUA_VTHREAD) {  /* threads must be watched */
        lua_State *th = gco2th(curr);
        linkgclist(th, g->grayagain);  /* insert into 'grayagain' list */
      }
      else if (curr->tt == LUA_VUPVAL && upisopen(gco2upv(curr)))
        set2gray(curr);  /* open upvalues are always gray */
      else  /* everything else is black */
        nw2black(curr);
      p = &curr->next;  /* go to next element */
    }
  }
}


/*
** Sweep for generational mode. Delete dead objects. (Because the
** collection is not incremental, there are no "new white" objects
** during the sweep. So, any white object must be dead.) For
** non-dead objects, advance their ages and clear the color of
** new objects. (Old objects keep their colors.)
** The ages of G_TOUCHED1 and G_TOUCHED2 objects cannot be advanced
** here, because these old-generation objects are usually not swept
** here.  They will all be advanced in 'correctgraylist'. That function
** will also remove objects turned white here from any gray list.
** 分代-忽略
*/
static GCObject **sweepgen (lua_State *L, global_State *g, GCObject **p,
                            GCObject *limit, GCObject **pfirstold1) {
  static const lu_byte nextage[] = {
    G_SURVIVAL,  /* from G_NEW */
    G_OLD1,      /* from G_SURVIVAL */
    G_OLD1,      /* from G_OLD0 */
    G_OLD,       /* from G_OLD1 */
    G_OLD,       /* from G_OLD (do not change) */
    G_TOUCHED1,  /* from G_TOUCHED1 (do not change) */
    G_TOUCHED2   /* from G_TOUCHED2 (do not change) */
  };
  int white = luaC_white(g);
  GCObject *curr;
  while ((curr = *p) != limit) {
    if (iswhite(curr)) {  /* is 'curr' dead? */
      lua_assert(!isold(curr) && isdead(g, curr));
      *p = curr->next;  /* remove 'curr' from list */
      freeobj(L, curr);  /* erase 'curr' */
    }
    else {  /* correct mark and age */
      if (getage(curr) == G_NEW) {  /* new objects go back to white */
        int marked = curr->marked & ~maskgcbits;  /* erase GC bits */
        curr->marked = cast_byte(marked | G_SURVIVAL | white);
      }
      else {  /* all other objects will be old, and so keep their color */
        setage(curr, nextage[getage(curr)]);
        if (getage(curr) == G_OLD1 && *pfirstold1 == NULL)
          *pfirstold1 = curr;  /* first OLD1 object in the list */
      }
      p = &curr->next;  /* go to next element */
    }
  }
  return p;
}


/*
** Traverse a list making all its elements white and clearing their
** age. In incremental mode, all objects are 'new' all the time,
** except for fixed strings (which are always old).
** 把链表里的所有对象都标记为白色
*/
static void whitelist (global_State *g, GCObject *p) {
  int white = luaC_white(g);
  for (; p != NULL; p = p->next)
    p->marked = cast_byte((p->marked & ~maskgcbits) | white);
}


/*
** Correct a list of gray objects. Return pointer to where rest of the
** list should be linked.
** Because this correction is done after sweeping, young objects might
** be turned white and still be in the list. They are only removed.
** 'TOUCHED1' objects are advanced to 'TOUCHED2' and remain on the list;
** Non-white threads also remain on the list; 'TOUCHED2' objects become
** regular old; they and anything else are removed from the list.
** 分代-忽略
*/
static GCObject **correctgraylist (GCObject **p) {
  GCObject *curr;
  while ((curr = *p) != NULL) {
    GCObject **next = getgclist(curr);
    if (iswhite(curr))
      goto remove;  /* remove all white objects */
    else if (getage(curr) == G_TOUCHED1) {  /* touched in this cycle? */
      lua_assert(isgray(curr));
      nw2black(curr);  /* make it black, for next barrier */
      changeage(curr, G_TOUCHED1, G_TOUCHED2);
      goto remain;  /* keep it in the list and go to next element */
    }
    else if (curr->tt == LUA_VTHREAD) {
      lua_assert(isgray(curr));
      goto remain;  /* keep non-white threads on the list */
    }
    else {  /* everything else is removed */
      lua_assert(isold(curr));  /* young objects should be white here */
      if (getage(curr) == G_TOUCHED2)  /* advance from TOUCHED2... */
        changeage(curr, G_TOUCHED2, G_OLD);  /* ... to OLD */
      nw2black(curr);  /* make object black (to be removed) */
      goto remove;
    }
    remove: *p = *next; continue;
    remain: p = next; continue;
  }
  return p;
}


/*
** Correct all gray lists, coalescing them into 'grayagain'.
** 分代-忽略
*/
static void correctgraylists (global_State *g) {
  GCObject **list = correctgraylist(&g->grayagain);
  *list = g->weak; g->weak = NULL;
  list = correctgraylist(list);
  *list = g->allweak; g->allweak = NULL;
  list = correctgraylist(list);
  *list = g->ephemeron; g->ephemeron = NULL;
  correctgraylist(list);
}


/*
** Mark black 'OLD1' objects when starting a new young collection.
** Gray objects are already in some gray list, and so will be visited
** in the atomic step.
** 分代-忽略
*/
static void markold (global_State *g, GCObject *from, GCObject *to) {
  GCObject *p;
  for (p = from; p != to; p = p->next) {
    if (getage(p) == G_OLD1) {
      lua_assert(!iswhite(p));
      changeage(p, G_OLD1, G_OLD);  /* now they are old */
      if (isblack(p))
        reallymarkobject(g, p);
    }
  }
}


/*
** Finish a young-generation collection.
** 分代-忽略
*/
static void finishgencycle (lua_State *L, global_State *g) {
  correctgraylists(g);
  checkSizes(L, g);
  g->gcstate = GCSpropagate;  /* skip restart */
  if (!g->gcemergency)
    callallpendingfinalizers(L);
}


/*
** Does a young collection. First, mark 'OLD1' objects. Then does the
** atomic step. Then, sweep all lists and advance pointers. Finally,
** finish the collection.
** 分代-忽略
*/
static void youngcollection (lua_State *L, global_State *g) {
  GCObject **psurvival;  /* to point to first non-dead survival object */
  GCObject *dummy;  /* dummy out parameter to 'sweepgen' */
  lua_assert(g->gcstate == GCSpropagate);
  if (g->firstold1) {  /* are there regular OLD1 objects? */
    markold(g, g->firstold1, g->reallyold);  /* mark them */
    g->firstold1 = NULL;  /* no more OLD1 objects (for now) */
  }
  markold(g, g->finobj, g->finobjrold);
  markold(g, g->tobefnz, NULL);
  atomic(L);

  /* sweep nursery and get a pointer to its last live element */
  g->gcstate = GCSswpallgc;
  psurvival = sweepgen(L, g, &g->allgc, g->survival, &g->firstold1);
  /* sweep 'survival' */
  sweepgen(L, g, psurvival, g->old1, &g->firstold1);
  g->reallyold = g->old1;
  g->old1 = *psurvival;  /* 'survival' survivals are old now */
  g->survival = g->allgc;  /* all news are survivals */

  /* repeat for 'finobj' lists */
  dummy = NULL;  /* no 'firstold1' optimization for 'finobj' lists */
  psurvival = sweepgen(L, g, &g->finobj, g->finobjsur, &dummy);
  /* sweep 'survival' */
  sweepgen(L, g, psurvival, g->finobjold1, &dummy);
  g->finobjrold = g->finobjold1;
  g->finobjold1 = *psurvival;  /* 'survival' survivals are old now */
  g->finobjsur = g->finobj;  /* all news are survivals */

  sweepgen(L, g, &g->tobefnz, NULL, &dummy);
  finishgencycle(L, g);
}


/*
** Clears all gray lists, sweeps objects, and prepare sublists to enter
** generational mode. The sweeps remove dead objects and turn all
** surviving objects to old. Threads go back to 'grayagain'; everything
** else is turned black (not in any gray list).
** 分代-忽略
*/
static void atomic2gen (lua_State *L, global_State *g) {
  cleargraylists(g);
  /* sweep all elements making them old */
  g->gcstate = GCSswpallgc;
  sweep2old(L, &g->allgc);
  /* everything alive now is old */
  g->reallyold = g->old1 = g->survival = g->allgc;
  g->firstold1 = NULL;  /* there are no OLD1 objects anywhere */

  /* repeat for 'finobj' lists */
  sweep2old(L, &g->finobj);
  g->finobjrold = g->finobjold1 = g->finobjsur = g->finobj;

  sweep2old(L, &g->tobefnz);

  g->gckind = KGC_GEN;
  g->lastatomic = 0;
  g->GCestimate = gettotalbytes(g);  /* base for memory control */
  finishgencycle(L, g);
}


/*
** Set debt for the next minor collection, which will happen when
** memory grows 'genminormul'%.
*/
static void setminordebt (global_State *g) {
  luaE_setdebt(g, -(cast(l_mem, (gettotalbytes(g) / 100)) * g->genminormul));
}


/*
** Enter generational mode. Must go until the end of an atomic cycle
** to ensure that all objects are correctly marked and weak tables
** are cleared. Then, turn all objects into old and finishes the
** collection.
** 分代-忽略
*/
static lu_mem entergen (lua_State *L, global_State *g) {
  lu_mem numobjs;
  luaC_runtilstate(L, bitmask(GCSpause));  /* prepare to start a new cycle */
  luaC_runtilstate(L, bitmask(GCSpropagate));  /* start new cycle */
  numobjs = atomic(L);  /* propagates all and then do the atomic stuff */
  atomic2gen(L, g);
  setminordebt(g);  /* set debt assuming next cycle will be minor */
  return numobjs;
}


/*
** Enter incremental mode. Turn all objects white, make all
** intermediate lists point to NULL (to avoid invalid pointers),
** and go to the pause state.
** 切换到增量gc模式时做的一些清理和初始化工作
*/
static void enterinc (global_State *g) {
  whitelist(g, g->allgc);
  g->reallyold = g->old1 = g->survival = NULL;
  whitelist(g, g->finobj);
  whitelist(g, g->tobefnz);
  g->finobjrold = g->finobjold1 = g->finobjsur = NULL;
  g->gcstate = GCSpause;
  g->gckind = KGC_INC;
  g->lastatomic = 0;
}


/*
** Change collector mode to 'newmode'.
** 修改gc的执行模式
*/
void luaC_changemode (lua_State *L, int newmode) {
  global_State *g = G(L);
  if (newmode != g->gckind) {
    if (newmode == KGC_GEN)  /* entering generational mode? */
      entergen(L, g);
    else
      enterinc(g);  /* entering incremental mode */
  }
  g->lastatomic = 0;
}


/*
** Does a full collection in generational mode.
** 分代-忽略
*/
static lu_mem fullgen (lua_State *L, global_State *g) {
  enterinc(g);
  return entergen(L, g);
}


/*
** Does a major collection after last collection was a "bad collection".
**
** When the program is building a big structure, it allocates lots of
** memory but generates very little garbage. In those scenarios,
** the generational mode just wastes time doing small collections, and
** major collections are frequently what we call a "bad collection", a
** collection that frees too few objects. To avoid the cost of switching
** between generational mode and the incremental mode needed for full
** (major) collections, the collector tries to stay in incremental mode
** after a bad collection, and to switch back to generational mode only
** after a "good" collection (one that traverses less than 9/8 objects
** of the previous one).
** The collector must choose whether to stay in incremental mode or to
** switch back to generational mode before sweeping. At this point, it
** does not know the real memory in use, so it cannot use memory to
** decide whether to return to generational mode. Instead, it uses the
** number of objects traversed (returned by 'atomic') as a proxy. The
** field 'g->lastatomic' keeps this count from the last collection.
** ('g->lastatomic != 0' also means that the last collection was bad.)
** 分代-忽略
*/
static void stepgenfull (lua_State *L, global_State *g) {
  lu_mem newatomic;  /* count of traversed objects */
  lu_mem lastatomic = g->lastatomic;  /* count from last collection */
  if (g->gckind == KGC_GEN)  /* still in generational mode? */
    enterinc(g);  /* enter incremental mode */
  luaC_runtilstate(L, bitmask(GCSpropagate));  /* start new cycle */
  newatomic = atomic(L);  /* mark everybody */
  if (newatomic < lastatomic + (lastatomic >> 3)) {  /* good collection? */
    atomic2gen(L, g);  /* return to generational mode */
    setminordebt(g);
  }
  else {  /* another bad collection; stay in incremental mode */
    g->GCestimate = gettotalbytes(g);  /* first estimate */
    entersweep(L);
    luaC_runtilstate(L, bitmask(GCSpause));  /* finish collection */
    setpause(g);
    g->lastatomic = newatomic;
  }
}


/*
** Does a generational "step".
** Usually, this means doing a minor collection and setting the debt to
** make another collection when memory grows 'genminormul'% larger.
**
** However, there are exceptions.  If memory grows 'genmajormul'%
** larger than it was at the end of the last major collection (kept
** in 'g->GCestimate'), the function does a major collection. At the
** end, it checks whether the major collection was able to free a
** decent amount of memory (at least half the growth in memory since
** previous major collection). If so, the collector keeps its state,
** and the next collection will probably be minor again. Otherwise,
** we have what we call a "bad collection". In that case, set the field
** 'g->lastatomic' to signal that fact, so that the next collection will
** go to 'stepgenfull'.
**
** 'GCdebt <= 0' means an explicit call to GC step with "size" zero;
** in that case, do a minor collection.
** 分代-忽略
*/
static void genstep (lua_State *L, global_State *g) {
  if (g->lastatomic != 0)  /* last collection was a bad one? */
    stepgenfull(L, g);  /* do a full step */
  else {
    lu_mem majorbase = g->GCestimate;  /* memory after last major collection */
    lu_mem majorinc = (majorbase / 100) * getgcparam(g->genmajormul);
    if (g->GCdebt > 0 && gettotalbytes(g) > majorbase + majorinc) {
      lu_mem numobjs = fullgen(L, g);  /* do a major collection */
      if (gettotalbytes(g) < majorbase + (majorinc / 2)) {
        /* collected at least half of memory growth since last major
           collection; keep doing minor collections. */
        lua_assert(g->lastatomic == 0);
      }
      else {  /* bad collection */
        g->lastatomic = numobjs;  /* signal that last collection was bad */
        setpause(g);  /* do a long wait for next (major) collection */
      }
    }
    else {  /* regular case; do a minor collection */
      youngcollection(L, g);
      setminordebt(g);
      g->GCestimate = majorbase;  /* preserve base value */
    }
  }
  lua_assert(isdecGCmodegen(g));
}

/* }====================================================== */


/*
** {======================================================
** GC control
** =======================================================
*/


/*
** Enter first sweep phase.
** The call to 'sweeptolive' makes the pointer point to an object
** inside the list (instead of to the header), so that the real sweep do
** not need to skip objects created between "now" and the start of the
** real sweep.
** 进入清理阶段；
** 1、切换到清理状态；
** 2、执行一次清理g->allgc，直到遇到第一个存活的对象；
*/
static void entersweep (lua_State *L) {
  global_State *g = G(L);
  g->gcstate = GCSswpallgc;
  lua_assert(g->sweepgc == NULL);
  g->sweepgc = sweeptolive(L, &g->allgc);
}


/*
** Delete all objects in list 'p' until (but not including) object
** 'limit'.
** 释放链表p里：从头到limit为止的所有对象
*/
static void deletelist (lua_State *L, GCObject *p, GCObject *limit) {
  while (p != limit) {
    GCObject *next = p->next;
    freeobj(L, p);
    p = next;
  }
}


/*
** Call all finalizers of the objects in the given Lua state, and
** then free all objects, except for the main thread.
** 关闭luastate时做的释放操作
*/
void luaC_freeallobjects (lua_State *L) {
  global_State *g = G(L);
  g->gcstp = GCSTPCLS;  /* no extra finalizers after here */
  luaC_changemode(L, KGC_INC);
  separatetobefnz(g, 1);  /* separate all objects with finalizers */
  lua_assert(g->finobj == NULL);
  callallpendingfinalizers(L);
  deletelist(L, g->allgc, obj2gco(g->mainthread));
  lua_assert(g->finobj == NULL);  /* no new finalizers */
  deletelist(L, g->fixedgc, NULL);  /* collect fixed objects */
  lua_assert(g->strt.nuse == 0);
}

/* 原子标记阶段，需要一次性执行完，不能分步 */
static lu_mem atomic (lua_State *L) {
  global_State *g = G(L);
  lu_mem work = 0;
  GCObject *origweak, *origall;
  GCObject *grayagain = g->grayagain;  /* save original list */
  g->grayagain = NULL;  /* 为啥先清掉，因为后面的流程可能会添加对象进去，避免重复 */
  lua_assert(g->ephemeron == NULL && g->weak == NULL); /* 为啥能成立?因为传播阶段是不会加到这2个链表里 */
  lua_assert(!iswhite(g->mainthread)); /* 主state肯定已经被标灰了，不是的话就是流程异常了 */
  g->gcstate = GCSatomic; 
  /* 标记正在运行的协程,这里为什么会标记L？
  ** 常规情况下，L==g->mainthread，即gc的step是在主state里触发的，这时L就是mainthread，前面mainthread已经标记过，所以这种情况L不会重复执行标记；
  ** 还有2种情况下，L!=g->mainthread:
  ** 1、lua中创建一个协程，在协程中创建新对象时，luaC_checkGC触发了gc的step，或者协程中主动调用了step；
  **    这个时候L在mainthread的虚拟栈里，如果L在mainthread遍历过后才创建并执行的，那么L是白色，并不会在传播阶段被遍历到，所以这里要主动标记一次，因为它也不能被释放；
  ** 2、在C中newthread，不会放到全局里，并且resume运行，如果函数内部触发了gc的step或者主动调用了step，这时L和mainthread也不同；
  */
  markobject(g, L);  /* mark running thread 标记正在运行的协程 */
  /* registry and global metatables may be changed by API 注册表可能被C端开发者修改 */
  markvalue(g, &g->l_registry);
  markmt(g);  /* mark global metatables 设置基本类型的全局metatable并没有设置 write barrier 在lua_setmetatable中*/
  work += propagateall(g);  /* empties 'gray' list 前面3个标记可能加入gray中*/
  /* remark occasional upvalues of (maybe) dead threads 重新标记可能已经是死亡状态的协程里的upvalues */
  work += remarkupvals(g);
  work += propagateall(g);  /* propagate changes remarkupvalues后gray可能有变化 */
  g->gray = grayagain;
  work += propagateall(g);  /* traverse 'grayagain' list 开始标记grayagain，该变的都变了，里面有弱表、瞬表、thread */
  convergeephemerons(g);
  /* at this point, all strongly accessible objects are marked. */
  /* 到了这一步，所有强引用的对象都已经被标记过了 */
  /* Clear values from weak tables, before checking finalizers */
  /* 先清理value没有被标记过的表，那种key没标记、value被标记的entry还未处理 */
  clearbyvalues(g, g->weak, NULL);
  clearbyvalues(g, g->allweak, NULL);
  origweak = g->weak; origall = g->allweak;
  separatetobefnz(g, 0);  /* separate objects to be finalized */
  work += markbeingfnz(g);  /* mark objects that will be finalized */
  work += propagateall(g);  /* remark, to propagate 'resurrection' 清空gray */
  /* 前面可能有finobj被标记过，这些finobj有可能引用到瞬表里的key或者value,所以又复活了，需要再收敛一边瞬表
  ** 可以参考例子：https://www.cnblogs.com/lindx/p/17590725.html
  **  local o1 = setmetatable({}, {__mode = "k"})
      local o2 = setmetatable({}, {__mode = "k"})
      local v1 = {}
      local v2 = {}
      local v3 = {}
      o1[v1] = v2
      o2[v2] = v3
      local t = setmetatable({[v1] = "aaa"}, {__gc = function ( )
	      print("__gc function call ...")
      end})
      v1 = nil
      v2 = nil
      v3 = nil
      t = nil
      collectgarbage() -- o1和o2还存活
      collectgarbage() -- o1和o2不存在了
  */
  convergeephemerons(g);
  /* at this point, all resurrected objects are marked. */
  /* 到这一步，所有复活的对象都已经被标记了 */
  /* remove dead objects from weak tables */
  clearbykeys(g, g->ephemeron);  /* clear keys from all ephemeron tables */
  clearbykeys(g, g->allweak);  /* clear keys from all 'allweak' tables */
  /* clear values from resurrected weak tables */
  /* 清理从保存origweak和origall到现在重新加到weak和allweak里面的对象，因为加入的对象都在头部，并且ori位置及后面的已经clearbyvalue了，所以只需要再清理新加的 */
  clearbyvalues(g, g->weak, origweak);
  clearbyvalues(g, g->allweak, origall);
  luaS_clearcache(g);
  g->currentwhite = cast_byte(otherwhite(g));  /* flip current white 翻转白色为另一个新对象的白色 */
  lua_assert(g->gray == NULL);
  return work;  /* estimate of slots marked by 'atomic' */
}

/* 遍历释放sweepgc里的所有白色对象，每次最多访问GCSWEEPMAX个
** 如果遍历完了，则进入下个状态
*/
static int sweepstep (lua_State *L, global_State *g,
                      int nextstate, GCObject **nextlist) {
  if (g->sweepgc) {
    l_mem olddebt = g->GCdebt;
    int count;
    g->sweepgc = sweeplist(L, g->sweepgc, GCSWEEPMAX, &count);
    g->GCestimate += g->GCdebt - olddebt;  /* update estimate */
    return count;
  }
  else {  /* enter next state */
    g->gcstate = nextstate;
    g->sweepgc = nextlist;
    return 0;  /* no work done */
  }
}

/* 核心的单步状态流程 */
static lu_mem singlestep (lua_State *L) {
  global_State *g = G(L);
  lu_mem work;
  lua_assert(!g->gcstopem);  /* collector is not reentrant 不能重入gc，如果gcstopem不为0，就是重入了*/
  g->gcstopem = 1;  /* no emergency collections while collecting 表示正在执行gc中*/
  switch (g->gcstate) {
    case GCSpause: {
      restartcollection(g);
      g->gcstate = GCSpropagate;
      work = 1;
      break;
    }
    case GCSpropagate: { /* 传播标记阶段 */
      if (g->gray == NULL) {  /* no more gray objects? */
        g->gcstate = GCSenteratomic;  /* finish propagate phase 所有gray对象都标记为了黑色，或者加入了对应的链表里 */
        work = 0;
      }
      else
        work = propagatemark(g);  /* traverse one gray object */
      break;
    }
    case GCSenteratomic: {
      work = atomic(L);  /* work is what was traversed by 'atomic' */
      entersweep(L); /* 设置到清理阶段，并清理一次 */
      g->GCestimate = gettotalbytes(g);  /* first estimate */
      break;
    }
    case GCSswpallgc: {  /* sweep "regular" objects */
      work = sweepstep(L, g, GCSswpfinobj, &g->finobj);
      break;
    }
    case GCSswpfinobj: {  /* sweep objects with finalizers */
      work = sweepstep(L, g, GCSswptobefnz, &g->tobefnz);
      break;
    }
    case GCSswptobefnz: {  /* sweep objects to be finalized */
      work = sweepstep(L, g, GCSswpend, NULL);
      break;
    }
    case GCSswpend: {  /* finish sweeps */
      checkSizes(L, g);
      g->gcstate = GCScallfin;
      work = 0;
      break;
    }
    case GCScallfin: {  /* call remaining finalizers 分步执行自定义的gc析构对象 */
      if (g->tobefnz && !g->gcemergency) {
        g->gcstopem = 0;  /* ok collections during finalizers */
        work = runafewfinalizers(L, GCFINMAX) * GCFINALIZECOST;
      }
      else {  /* emergency mode or no more finalizers */
        g->gcstate = GCSpause;  /* finish collection */
        work = 0;
      }
      break;
    }
    default: lua_assert(0); return 0;
  }
  g->gcstopem = 0;
  return work;
}


/*
** advances the garbage collector until it reaches a state allowed
** by 'statemask'
*/
void luaC_runtilstate (lua_State *L, int statesmask) {
  global_State *g = G(L);
  while (!testbit(statesmask, g->gcstate))
    singlestep(L);
}



/*
** Performs a basic incremental step. The debt and step size are
** converted from bytes to "units of work"; then the function loops
** running single steps until adding that many units of work or
** finishing a cycle (pause state). Finally, it sets the debt that
** controls when next step will be performed.
** g->gcstepmul默认值是100、g->gcstepsize默认值是13，对应2^13=8192,即8kb、g->gcpause默认值是200
** 见fullinc的注解
*/
static void incstep (lua_State *L, global_State *g) {
  int stepmul = (getgcparam(g->gcstepmul) | 1);  /* avoid division by 0 */
  l_mem debt = (g->GCdebt / WORK2MEM) * stepmul;
  l_mem stepsize = (g->gcstepsize <= log2maxs(l_mem))
                 ? ((cast(l_mem, 1) << g->gcstepsize) / WORK2MEM) * stepmul
                 : MAX_LMEM;  /* overflow; keep maximum value */
  do {  /* repeat until pause or enough "credit" (negative debt) */
    lu_mem work = singlestep(L);  /* perform one single step */
    debt -= work;
  } while (debt > -stepsize && g->gcstate != GCSpause);
  if (g->gcstate == GCSpause)
    setpause(g);  /* pause until next cycle */
  else {
    debt = (debt / stepmul) * WORK2MEM;  /* convert 'work units' to bytes */
    luaE_setdebt(g, debt);
  }
}

/*
** Performs a basic GC step if collector is running. (If collector is
** not running, set a reasonable debt to avoid it being called at
** every single check.)
** 执行一次gc步进：如果已经在gc中，那么正常step一次；如果gc没运行，设置个固定的debt，避免每次调用step的时候都执行
*/
void luaC_step (lua_State *L) {
  global_State *g = G(L);
  if (!gcrunning(g))  /* not running? */
    luaE_setdebt(g, -2000);
  else {
    if(isdecGCmodegen(g))
      genstep(L, g);
    else
      incstep(L, g);
  }
}


/*
** Perform a full collection in incremental mode.
** Before running the collection, check 'keepinvariant'; if it is true,
** there may be some objects marked as black, so the collector has
** to sweep all objects to turn them back to white (as white has not
** changed, nothing will be collected).
** g->gcstepmul默认值是100、g->gcstepsize默认值是13，对应2^13=8192,即8kb、g->gcpause默认值是200
** 举例看这几个变量的变化过程：
** 假设初始创建了state之后，totalbytes = sizeof(LG); x64上：1552个字节；GCdebt=0;
** 创建2个空的table，GCdebt=56*2=112，其中一个设置为nil，让gc进行回收，手动调用一次fullgc；
** 执行到atomic阶段之后，会计算一次GCestimate = gettotalbytes(g) = 1552 + 112 = 1664;
** 之后是sweap释放阶段，nil的table内存会被释放，那么GCdebt=56，GCestimate=1664-56=1608；
** 执行完callfin之后，满足GCestimate == gettotalbytes(g)，都是1608；
** 调用setpause：pause=800;estimate = g->GCestimate / PAUSEADJ = 16;threshold=16*800=12800;
** debt = 1608-12800=-11192;
** 调用setdebt：tb=1608，不满足debt<tb-MAX_LMEM条件，那么totalbytes=1608+11192=12800；GCdebt=-11192；
** 那么下一次gcstep自动触发的条件是GCdebt>0,也就是说在至少分配了11192个字节后，会触发gcstep；
** 调用incstep：
**  1、假如这期间申请了700个TValue对象，此时，GCdebt=700*16-11192=8；
**     stepmul=401,debt=0,stepsize=512*401=205312,
**     执行do循环，debt一直减小，一直到debt<-205312或者pause了，按这里的数值计算，会到pause退出，因为分配的新字节数小于stepsize的，
**     又调用setpause，重新计算值，加入700个对象全回收，再计算的值和之前一样；
**  2、假如这期间申请了相当于1000个TValue对象，此时，GCdebt=1000*16-11192=4808
**     stepmul=401,debt=4808*401=1928008,stepsize=512*401=205312;
**     执行do循环，debt一直减小,假如满足debt<-stepsize退出，说明对象较多，单步回收不完；
**     重新计算下一次step的debt：假如退出do时，debt=-205328，则，debt=（-205328/401）*16=-8192；
**     又调用setdebt；
**  GCdebt：初始为0，大于0的时候触发单步gc，这之后一直保持负数，新分配的内存值累加到上面，直到大于0触发step，为负数表示允许分配多少内存才触发gcstep；
**  gcstepmul:执行单步回收的内存大小倍数，值越大，单次处理的对象就越多，耗时就越长；
**  gcpause：每次gc执行完后会调用setpause，计算下一次gc触发的debt，这个值越大，那么下次gcstep触发的debt就越大，通常是当前内存值得倍数，
**           比如200时，debt=-estimate，totalbytes=2*estimate，即新分配的内存等于上一次gc后还占用的总内存时，触发新一轮gc；
**  执行完一次gc后： GCestimate == gettotalbytes(g)，
** 执行一次全量gc
** 1、如果当前在atomic阶段之前，那么跳过atomic状态，进入allgc阶段，并一直执行到pause阶段，把所有对象恢复成白色，因为没有执行atomic就不会翻转白色；
** 2、开启新的一轮gc，会跳过propagate这个传播标记阶段，因为atomic阶段会遍历完所有对象；所以当分步执行的时候，propagate阶段分步标记了对象，可以减轻atomic的压力；
** 3、调用setpause，计算下一次gc触发的debt；
*/
static void fullinc (lua_State *L, global_State *g) {
  if (keepinvariant(g))  /* black objects? 如果是还在标记阶段 */
    entersweep(L); /* sweep everything to turn them back to white 全部 */
  /* finish any pending sweep phase to start a new cycle */
  luaC_runtilstate(L, bitmask(GCSpause));
  luaC_runtilstate(L, bitmask(GCSpropagate));  /* start new cycle */
  g->gcstate = GCSenteratomic;  /* go straight to atomic phase */
  luaC_runtilstate(L, bitmask(GCScallfin));  /* run up to finalizers */
  /* estimate must be correct after a full GC cycle */
  lua_assert(g->GCestimate == gettotalbytes(g));
  luaC_runtilstate(L, bitmask(GCSpause));  /* finish collection */
  setpause(g);
}


/*
** Performs a full GC cycle; if 'isemergency', set a flag to avoid
** some operations which could change the interpreter state in some
** unexpected ways (running finalizers and shrinking some structures).
** 执行一次全量gc；
** emergency collection：当内存分配失败时，会强制执行一次完整的紧急垃圾收集，然后再尝试分配
*/
void luaC_fullgc (lua_State *L, int isemergency) {
  global_State *g = G(L);
  lua_assert(!g->gcemergency);
  g->gcemergency = isemergency;  /* set flag */
  if (g->gckind == KGC_INC)
    fullinc(L, g);
  else
    fullgen(L, g);
  g->gcemergency = 0;
}

/* }====================================================== */


