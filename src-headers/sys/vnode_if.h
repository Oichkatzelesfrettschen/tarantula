#pragma once
#ifndef _SRC_HEADERS_VNODE_IF_H_
#define _SRC_HEADERS_VNODE_IF_H_
/*
 * Placeholder vnode interface definitions for user-space builds.
 * The real header is generated from vnode_if.src in the kernel tree.
 */
struct vnode;
struct vop_bwrite_args; /* opaque for prototypes */
extern int vnodeop_desc_stub;
#endif /* _SRC_HEADERS_VNODE_IF_H_ */
