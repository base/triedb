import { useState, useCallback } from 'react';
import type { ExplorerNode, PageInfo, PathSearchResult } from '../types';
import * as api from '../api/client';

export interface PageData {
  info: PageInfo;
  nodes: ExplorerNode[];
}

export interface TrieState {
  loadedPages: Map<number, PageData>;
  pagePaths: Map<number, string>; // Base path for each page's root
  childPages: Set<number>; // Pages loaded as children of other nodes (not shown at top level)
  expandedNodes: Set<string>;
  selectedNode: { pageId: number; cellIndex: number } | null;
  autoExpand: boolean; // Auto-expand nodes as pages are loaded
  showEmptySlots: boolean; // Show empty child slots in branches
  showHashes: boolean; // Show RLP hashes alongside pointers
  isLoading: boolean;
  error: string | null;
}

export function useTrieData() {
  const [state, setState] = useState<TrieState>({
    loadedPages: new Map(),
    pagePaths: new Map(),
    childPages: new Set(),
    expandedNodes: new Set(),
    selectedNode: null,
    autoExpand: false,
    showEmptySlots: false,
    showHashes: false,
    isLoading: false,
    error: null,
  });

  const loadRootPage = useCallback(async () => {
    setState(s => ({ ...s, isLoading: true, error: null }));
    try {
      const response = await api.getRoot();
      if (!response.success) {
        throw new Error(response.error || 'Failed to load root page');
      }
      if (response.data?.page) {
        const pageId = response.data.rootPageId!;
        setState(s => ({
          ...s,
          loadedPages: new Map([[pageId, response.data!.page!]]),
          pagePaths: new Map([[pageId, '']]), // Root page has empty base path
          isLoading: false,
        }));
      } else {
        setState(s => ({ ...s, isLoading: false }));
      }
    } catch (e) {
      setState(s => ({
        ...s,
        isLoading: false,
        error: e instanceof Error ? e.message : 'Unknown error',
      }));
    }
  }, []);

  const loadPage = useCallback(async (pageId: number, basePath?: string, isChildPage: boolean = false) => {
    setState(s => ({ ...s, isLoading: true, error: null }));
    try {
      const response = await api.getPage(pageId);
      if (!response.success) {
        throw new Error(response.error || 'Failed to load page');
      }
      if (response.data) {
        setState(s => {
          const newPages = new Map(s.loadedPages);
          newPages.set(pageId, response.data!);
          const newPaths = new Map(s.pagePaths);
          if (basePath !== undefined) {
            newPaths.set(pageId, basePath);
          }
          const newChildPages = new Set(s.childPages);
          if (isChildPage) {
            newChildPages.add(pageId);
          }
          // Auto-expand all nodes on this page if autoExpand is enabled
          const newExpanded = new Set(s.expandedNodes);
          if (s.autoExpand && response.data) {
            for (const node of response.data.nodes) {
              newExpanded.add(`${pageId}:${node.cellIndex}`);
            }
          }
          return { ...s, loadedPages: newPages, pagePaths: newPaths, childPages: newChildPages, expandedNodes: newExpanded, isLoading: false };
        });
      }
    } catch (e) {
      setState(s => ({
        ...s,
        isLoading: false,
        error: e instanceof Error ? e.message : 'Unknown error',
      }));
    }
  }, []);

  const toggleNode = useCallback((pageId: number, cellIndex: number) => {
    const key = `${pageId}:${cellIndex}`;
    setState(s => {
      const newExpanded = new Set(s.expandedNodes);
      if (newExpanded.has(key)) {
        newExpanded.delete(key);
      } else {
        newExpanded.add(key);
      }
      return { ...s, expandedNodes: newExpanded };
    });
  }, []);

  const selectNode = useCallback((pageId: number, cellIndex: number) => {
    setState(s => ({
      ...s,
      selectedNode: { pageId, cellIndex },
    }));
  }, []);

  const isNodeExpanded = useCallback(
    (pageId: number, cellIndex: number) => {
      return state.expandedNodes.has(`${pageId}:${cellIndex}`);
    },
    [state.expandedNodes]
  );

  const isPageLoaded = useCallback(
    (pageId: number) => {
      return state.loadedPages.has(pageId);
    },
    [state.loadedPages]
  );

  const getPageBasePath = useCallback(
    (pageId: number) => {
      return state.pagePaths.get(pageId) ?? '';
    },
    [state.pagePaths]
  );

  // Load pages along a search path, computing proper base paths and expanding nodes
  const loadSearchPath = useCallback(async (result: PathSearchResult) => {
    setState(s => ({ ...s, isLoading: true, error: null }));

    try {
      const newPages = new Map(state.loadedPages);
      const newPaths = new Map(state.pagePaths);
      const newChildPages = new Set(state.childPages);
      const newExpanded = new Set(state.expandedNodes);

      let currentPath = '';
      let lastPageId: number | null = null;

      // Process each node in the path
      for (const node of result.pathToNode) {
        const pageId = node.pageId;

        // Load page if not already loaded
        if (!newPages.has(pageId)) {
          const response = await api.getPage(pageId);
          if (response.success && response.data) {
            newPages.set(pageId, response.data);
          }
        }

        // Set base path for this page if it's a new page in the traversal
        if (lastPageId !== null && pageId !== lastPageId) {
          // This is a child page - mark it and set path
          newPaths.set(pageId, currentPath);
          newChildPages.add(pageId);
        } else if (lastPageId === null) {
          // First page (root) - set empty base path
          newPaths.set(pageId, '');
        }

        // Expand this node
        newExpanded.add(`${pageId}:${node.cellIndex}`);

        // Update current path with this node's prefix
        currentPath += node.prefix || '';

        // If this is a branch, add the nibble for the next node
        if (node.nodeType === 'Branch' && node.children) {
          // Find which child leads to the next node in the path
          const nodeIndex = result.pathToNode.indexOf(node);
          if (nodeIndex < result.pathToNode.length - 1) {
            const nextNode = result.pathToNode[nodeIndex + 1];
            for (const child of node.children) {
              if (child.pointer.locationType === 'SamePage' && child.pointer.cellIndex === nextNode.cellIndex) {
                currentPath += child.index.toString(16).toUpperCase();
                break;
              } else if (child.pointer.locationType === 'OtherPage' && child.pointer.pageId === nextNode.pageId) {
                currentPath += child.index.toString(16).toUpperCase();
                break;
              }
            }
          }
        }

        lastPageId = pageId;
      }

      setState(s => ({
        ...s,
        loadedPages: newPages,
        pagePaths: newPaths,
        childPages: newChildPages,
        expandedNodes: newExpanded,
        isLoading: false,
      }));
    } catch (e) {
      setState(s => ({
        ...s,
        isLoading: false,
        error: e instanceof Error ? e.message : 'Unknown error',
      }));
    }
  }, [state.loadedPages, state.pagePaths, state.childPages, state.expandedNodes]);

  const toggleAutoExpand = useCallback(() => {
    setState(s => ({ ...s, autoExpand: !s.autoExpand }));
  }, []);

  const toggleShowEmptySlots = useCallback(() => {
    setState(s => ({ ...s, showEmptySlots: !s.showEmptySlots }));
  }, []);

  const toggleShowHashes = useCallback(() => {
    setState(s => ({ ...s, showHashes: !s.showHashes }));
  }, []);

  const expandAllOnPage = useCallback((pageId: number) => {
    setState(s => {
      const pageData = s.loadedPages.get(pageId);
      if (!pageData) return s;
      const newExpanded = new Set(s.expandedNodes);
      for (const node of pageData.nodes) {
        newExpanded.add(`${pageId}:${node.cellIndex}`);
      }
      return { ...s, expandedNodes: newExpanded };
    });
  }, []);

  const collapseAllOnPage = useCallback((pageId: number) => {
    setState(s => {
      const pageData = s.loadedPages.get(pageId);
      if (!pageData) return s;
      const newExpanded = new Set(s.expandedNodes);
      for (const node of pageData.nodes) {
        newExpanded.delete(`${pageId}:${node.cellIndex}`);
      }
      return { ...s, expandedNodes: newExpanded };
    });
  }, []);

  return {
    state,
    loadRootPage,
    loadPage,
    toggleNode,
    selectNode,
    isNodeExpanded,
    isPageLoaded,
    getPageBasePath,
    loadSearchPath,
    toggleAutoExpand,
    toggleShowEmptySlots,
    toggleShowHashes,
    expandAllOnPage,
    collapseAllOnPage,
  };
}
