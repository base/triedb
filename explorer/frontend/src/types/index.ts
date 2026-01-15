export interface ExplorerPointer {
  locationType: 'SamePage' | 'OtherPage' | 'Unknown';
  cellIndex?: number;
  pageId?: number;
  rlpHash?: string;
}

export interface ChildEntry {
  index: number;
  pointer: ExplorerPointer;
}

export interface ExplorerNode {
  pageId: number;
  cellIndex: number;
  prefix: string;
  nodeType: 'AccountLeaf' | 'StorageLeaf' | 'Branch';
  sizeBytes: number;
  nonce?: number;
  balance?: string;
  codeHash?: string;
  storageRoot?: ExplorerPointer;
  value?: string;
  children?: ChildEntry[];
}

// Tree node that wraps ExplorerNode with resolved children
export interface TreeNode {
  node: ExplorerNode;
  localChildren: TreeNode[];
  basePath: string;
  isStorageChild?: boolean; // True if this subtree is storage for an account
}

export interface PageInfo {
  pageId: number;
  snapshotId: number;
  totalBytes: number;
  usedBytes: number;
  freeBytes: number;
  cellCount: number;
  occupancyPercent: number;
}

export interface OrphanPageInfo {
  pageId: number;
  orphanedAtSnapshot: number;
}

export interface DatabaseInfo {
  snapshotId: number;
  rootNodeHash: string;
  rootNodePageId: number | null;
  totalPageCount: number;
  orphanedPages: OrphanPageInfo[];
}

export interface PathSearchResult {
  matchedPath: string;
  node: ExplorerNode;
  pathToNode: ExplorerNode[];
}

export interface ApiResponse<T> {
  success: boolean;
  data?: T;
  error?: string;
}

export interface PageResponse {
  info: PageInfo;
  nodes: ExplorerNode[];
}

export interface RootResponse {
  rootPageId: number | null;
  page: PageResponse | null;
}

export interface DescendantsResponse {
  pageId: number;
  nodes: ExplorerNode[];
}
