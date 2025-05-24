# Kernel Memory Allocator

This note describes the planned memory allocation mechanisms used by the microkernel and its servers.

## Slab-style allocator with per-CPU caches

Each CPU maintains its own slab cache holding small objects grouped by size class. Slabs are carved from contiguous pages and refilled from a global pool when exhausted. Metadata lives outside the slab pages so that cache lines remain focused on objects.

## Physical page allocator for IOMMU mappings

Drivers that require DMA-capable memory obtain pages from a dedicated physical allocator. It tracks contiguous page runs and provides alignment suitable for IOMMU mapping. The allocator integrates with the VM subsystem but bypasses higher-level caches.

## Emergency reserves

Critical paths such as interrupt handlers rely on a small reserve of preallocated pages. These reserves are replenished in the background so that allocation rarely fails even under memory pressure. Calls fall back to the emergency pool after the per-CPU and global caches are drained.

