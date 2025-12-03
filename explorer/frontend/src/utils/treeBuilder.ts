import type { ExplorerNode, TreeNode } from '../types';

/**
 * Build a tree structure from a flat list of nodes.
 * Cell 0 is always the canonical root of a page's subtrie.
 * Also handles same-page storage root references for account leaves.
 */
export function buildTree(nodes: ExplorerNode[], basePath: string): TreeNode[] {
  // Create a map from cellIndex -> node for quick lookup
  const nodeMap = new Map<number, ExplorerNode>();
  for (const node of nodes) {
    nodeMap.set(node.cellIndex, node);
  }

  // Cell 0 is always the root of a page's subtrie
  const rootNode = nodeMap.get(0);
  if (!rootNode) {
    // No root node found - page may be empty or corrupted
    return [];
  }

  // Recursively build tree nodes
  function buildTreeNode(node: ExplorerNode, currentPath: string, isStorageSubtree: boolean = false): TreeNode {
    const nodePath = currentPath + (node.prefix || '');
    const localChildren: TreeNode[] = [];

    if (node.nodeType === 'Branch' && node.children) {
      for (const child of node.children) {
        if (child.pointer.locationType === 'SamePage' && child.pointer.cellIndex !== undefined) {
          const childNode = nodeMap.get(child.pointer.cellIndex);
          if (childNode) {
            const nibble = child.index.toString(16).toUpperCase();
            localChildren.push(buildTreeNode(childNode, nodePath + nibble, isStorageSubtree));
          }
        }
      }
    }

    // Handle same-page storage root for account leaves
    if (node.nodeType === 'AccountLeaf' && node.storageRoot) {
      if (node.storageRoot.locationType === 'SamePage' && node.storageRoot.cellIndex !== undefined) {
        const storageNode = nodeMap.get(node.storageRoot.cellIndex);
        if (storageNode) {
          // Storage tries start fresh with empty path
          const storageTreeNode = buildTreeNode(storageNode, '', true);
          storageTreeNode.isStorageChild = true;
          localChildren.push(storageTreeNode);
        }
      }
    }

    return {
      node,
      localChildren,
      basePath: currentPath,
    };
  }

  return [buildTreeNode(rootNode, basePath)];
}
