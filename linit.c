/*
** $Id: linit.c $
** Initialization of libraries for lua.c and other clients
** See Copyright Notice in lua.h
*/


#define linit_c
#define LUA_LIB

/*
** If you embed Lua in your program and need to open the standard
** libraries, call luaL_openlibs in your program. If you need a
** different set of libraries, copy this file to your project and edit
** it to suit your needs.
**
** You can also *preload* libraries, so that a later 'require' can
** open the library, which is already linked to the application.
** For that, do the following code:
**
**  luaL_getsubtable(L, LUA_REGISTRYINDEX, LUA_PRELOAD_TABLE);
**  lua_pushcfunction(L, luaopen_modname);
**  lua_setfield(L, -2, modname);
**  lua_pop(L, 1);  // remove PRELOAD table
*/

#include "lprefix.h"


#include <stddef.h>

#include "lua.h"

#include "lualib.h"
#include "lauxlib.h"


/*
** these libs are loaded by lua.c and are readily available to any Lua
** program
** 执行各自的库初始化，会在_LOADED表中标记是否已经加载过，下面这些接口都是返回的1，所以_LOADED[name] = 1 表示已经加载过
*/
static const luaL_Reg loadedlibs[] = {
  {LUA_GNAME, luaopen_base},
  {LUA_LOADLIBNAME, luaopen_package},
  {LUA_COLIBNAME, luaopen_coroutine},
  {LUA_TABLIBNAME, luaopen_table},
  {LUA_IOLIBNAME, luaopen_io},
  {LUA_OSLIBNAME, luaopen_os},
  {LUA_STRLIBNAME, luaopen_string},
  {LUA_MATHLIBNAME, luaopen_math},
  {LUA_UTF8LIBNAME, luaopen_utf8},
  {LUA_DBLIBNAME, luaopen_debug},
  {NULL, NULL}
};

/*
** 创建state后执行的第一个函数，注册基础库
*/
LUALIB_API void luaL_openlibs (lua_State *L) {
  const luaL_Reg *lib;
  /* "require" functions from 'loadedlibs' and set results to global table */
  for (lib = loadedlibs; lib->func; lib++) {
    luaL_requiref(L, lib->name, lib->func, 1);  /* 判断库是否已经加载，没有加载则调用func加载，返回后把func的返回值压在栈顶，以上几个返回值都是1，而不是一个table */
    lua_pop(L, 1);  /* remove lib 弹出返回值，恢复栈 */
  }
}

