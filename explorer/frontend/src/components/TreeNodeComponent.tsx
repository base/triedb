import { useMemo, useState } from 'react';
import type { ExplorerNode, PageInfo, TreeNode, ChildEntry } from '../types';
import { buildTree } from '../utils/treeBuilder';

function getFullnessColor(percent: number): string {
  const hue = Math.max(0, 120 - percent * 1.2);
  return `hsl(${hue}, 60%, 92%)`;
}

function copyToClipboard(text: string): Promise<void> {
  return navigator.clipboard.writeText(text);
}

interface TreeNodeComponentProps {
  treeNode: TreeNode;
  depth: number;
  accountPath: string; // Path of parent account (for storage nodes)
  expandedNodes: Set<string>;
  loadedPages: Map<number, { info: PageInfo; nodes: ExplorerNode[] }>;
  pagePaths: Map<number, string>;
  showEmptySlots: boolean;
  showHashes: boolean;
  onToggleNode: (pageId: number, cellIndex: number) => void;
  onNavigate: (pageId: number, basePath?: string, isChildPage?: boolean) => void;
  onExpandAllOnPage: (pageId: number) => void;
  onCollapseAllOnPage: (pageId: number) => void;
}

export function TreeNodeComponent({
  treeNode,
  depth,
  accountPath,
  expandedNodes,
  loadedPages,
  pagePaths,
  showEmptySlots,
  showHashes,
  onToggleNode,
  onNavigate,
  onExpandAllOnPage,
  onCollapseAllOnPage,
}: TreeNodeComponentProps) {
  const { node, localChildren, basePath } = treeNode;
  const fullPath = basePath + (node.prefix || '');
  // For storage nodes, prepend the account path
  const displayPath = accountPath ? `${accountPath}:${fullPath}` : fullPath;
  const isExpanded = expandedNodes.has(`${node.pageId}:${node.cellIndex}`);
  const nodeTypeClass = node.nodeType.toLowerCase().replace('leaf', '-leaf');
  const [copied, setCopied] = useState(false);

  const handleCopyPath = (e: React.MouseEvent) => {
    e.stopPropagation();
    const pathToCopy = displayPath ? `0x${displayPath}` : '';
    if (pathToCopy) {
      copyToClipboard(pathToCopy).then(() => {
        setCopied(true);
        setTimeout(() => setCopied(false), 1500);
      });
    }
  };

  // Check if this node has any expandable content
  const hasLocalChildren = localChildren.length > 0;
  const hasRemoteChildren = node.nodeType === 'Branch' && node.children?.some(
    c => c.pointer.locationType === 'OtherPage'
  );
  const hasStorageRoot = node.nodeType === 'AccountLeaf' && node.storageRoot?.locationType === 'OtherPage';
  const hasExpandableContent = hasLocalChildren || hasRemoteChildren || hasStorageRoot ||
    node.nodeType === 'AccountLeaf' || node.nodeType === 'StorageLeaf';

  // Build sorted list of all children (local + remote) by index for branches
  const sortedBranchChildren = useMemo(() => {
    if (node.nodeType !== 'Branch' || !node.children) return [];

    // Create a map of index -> child info
    const childMap = new Map<number, { type: 'local' | 'remote' | 'empty'; child?: ChildEntry; treeNode?: TreeNode }>();

    // Initialize all 16 slots as empty if showing empty slots
    if (showEmptySlots) {
      for (let i = 0; i < 16; i++) {
        childMap.set(i, { type: 'empty' });
      }
    }

    // Add remote children
    for (const child of node.children) {
      if (child.pointer.locationType === 'OtherPage') {
        childMap.set(child.index, { type: 'remote', child });
      }
    }

    // Add local children (override if exists)
    for (const treeChild of localChildren) {
      if (!treeChild.isStorageChild) {
        // Find the nibble for this child from the parent's children array
        const childEntry = node.children.find(c =>
          c.pointer.locationType === 'SamePage' &&
          c.pointer.cellIndex === treeChild.node.cellIndex
        );
        if (childEntry) {
          childMap.set(childEntry.index, { type: 'local', child: childEntry, treeNode: treeChild });
        }
      }
    }

    // Sort by index and return
    return Array.from(childMap.entries())
      .sort((a, b) => a[0] - b[0])
      .map(([index, data]) => ({ index, ...data }));
  }, [node, localChildren, showEmptySlots]);

  // Get storage children (local) separately
  const storageChildren = localChildren.filter(c => c.isStorageChild);

  return (
    <div className="tree-node" style={{ marginLeft: depth * 20 }}>
      <div className="node-header" onClick={() => onToggleNode(node.pageId, node.cellIndex)}>
        {hasExpandableContent ? (
          <span className={`expand-icon ${isExpanded ? 'expanded' : ''}`}>&#9654;</span>
        ) : (
          <span className="expand-icon-placeholder" />
        )}
        <span className={`node-type ${nodeTypeClass}`}>{node.nodeType}</span>
        <span
          className={`node-path ${displayPath ? 'clickable' : ''} ${copied ? 'copied' : ''}`}
          onClick={displayPath ? handleCopyPath : undefined}
          title={displayPath ? 'Click to copy path' : undefined}
        >
          {displayPath ? (
            <>
              0x{accountPath && <span className="path-account">{accountPath}:</span>}
              {basePath && <span className="path-base">{basePath}</span>}
              {node.prefix && <span className="path-prefix">{node.prefix}</span>}
              {copied && <span className="copy-feedback">Copied!</span>}
            </>
          ) : (
            '(root)'
          )}
        </span>
        <span className="node-location">
          Cell {node.cellIndex} | {node.sizeBytes} bytes
        </span>
      </div>

      {isExpanded && (
        <div className="node-content">
          {/* Node details (account/storage leaf values) */}
          {(node.nodeType === 'AccountLeaf' || node.nodeType === 'StorageLeaf') && (
            <div className="node-details">
              <dl>
                {node.nodeType === 'AccountLeaf' && (
                  <>
                    <dt>Nonce</dt>
                    <dd>{node.nonce}</dd>
                    <dt>Balance</dt>
                    <dd>{node.balance}</dd>
                    <dt>Code Hash</dt>
                    <dd>0x{node.codeHash}</dd>
                  </>
                )}
                {node.nodeType === 'StorageLeaf' && (
                  <>
                    <dt>Value</dt>
                    <dd>{node.value}</dd>
                  </>
                )}
              </dl>
            </div>
          )}

          {/* Branch children - sorted by index */}
          {node.nodeType === 'Branch' && sortedBranchChildren.length > 0 && (
            <div className="branch-children">
              {sortedBranchChildren.map(({ index, type, child, treeNode: childTreeNode }) => {
                const nibble = index.toString(16).toUpperCase();

                if (type === 'empty') {
                  return (
                    <div key={index} className="empty-slot" style={{ marginLeft: (depth + 1) * 20 }}>
                      <span className="slot-nibble">[{nibble}]</span>
                      <span className="slot-empty">—</span>
                    </div>
                  );
                }

                if (type === 'local' && childTreeNode) {
                  return (
                    <div key={index} className="local-child-wrapper">
                      <div className="child-nibble-label" style={{ marginLeft: (depth + 1) * 20 }}>
                        <span className="slot-nibble">[{nibble}]</span>
                        {showHashes && child?.pointer.rlpHash && (
                          <span className="pointer-hash" title={child.pointer.rlpHash}>
                            {child.pointer.rlpHash}
                          </span>
                        )}
                      </div>
                      <TreeNodeComponent
                        treeNode={childTreeNode}
                        depth={depth + 1}
                        accountPath={accountPath}
                        expandedNodes={expandedNodes}
                        loadedPages={loadedPages}
                        pagePaths={pagePaths}
                        showEmptySlots={showEmptySlots}
                        showHashes={showHashes}
                        onToggleNode={onToggleNode}
                        onNavigate={onNavigate}
                        onExpandAllOnPage={onExpandAllOnPage}
                        onCollapseAllOnPage={onCollapseAllOnPage}
                      />
                    </div>
                  );
                }

                if (type === 'remote' && child) {
                  return (
                    <RemoteChildPointer
                      key={index}
                      child={child}
                      parentPath={fullPath}
                      accountPath={accountPath}
                      loadedPages={loadedPages}
                      pagePaths={pagePaths}
                      expandedNodes={expandedNodes}
                      showEmptySlots={showEmptySlots}
                      showHashes={showHashes}
                      onNavigate={onNavigate}
                      onToggleNode={onToggleNode}
                      onExpandAllOnPage={onExpandAllOnPage}
                      onCollapseAllOnPage={onCollapseAllOnPage}
                      depth={depth + 1}
                    />
                  );
                }

                return null;
              })}
            </div>
          )}

          {/* Local storage children */}
          {storageChildren.map((child) => (
            <div key={`storage-${child.node.pageId}:${child.node.cellIndex}`} className="storage-child-wrapper">
              <div className="storage-child-label" style={{ marginLeft: (depth + 1) * 20 }}>
                <span className="storage-label">Storage</span>
              </div>
              <TreeNodeComponent
                treeNode={child}
                depth={depth + 1}
                accountPath={fullPath}
                expandedNodes={expandedNodes}
                loadedPages={loadedPages}
                pagePaths={pagePaths}
                showEmptySlots={showEmptySlots}
                showHashes={showHashes}
                onToggleNode={onToggleNode}
                onNavigate={onNavigate}
                onExpandAllOnPage={onExpandAllOnPage}
                onCollapseAllOnPage={onCollapseAllOnPage}
              />
            </div>
          ))}

          {/* Remote storage root for account leaves */}
          {node.nodeType === 'AccountLeaf' && node.storageRoot &&
           node.storageRoot.locationType === 'OtherPage' &&
           node.storageRoot.pageId !== undefined && (
            <div className="storage-root-section" style={{ marginLeft: (depth + 1) * 20 }}>
              <StorageRootPointer
                pageId={node.storageRoot.pageId}
                rlpHash={node.storageRoot.rlpHash}
                accountPath={fullPath}
                loadedPages={loadedPages}
                pagePaths={pagePaths}
                expandedNodes={expandedNodes}
                showEmptySlots={showEmptySlots}
                showHashes={showHashes}
                onNavigate={onNavigate}
                onToggleNode={onToggleNode}
                onExpandAllOnPage={onExpandAllOnPage}
                onCollapseAllOnPage={onCollapseAllOnPage}
                depth={depth + 1}
              />
            </div>
          )}
        </div>
      )}
    </div>
  );
}

interface RemoteChildPointerProps {
  child: ChildEntry;
  parentPath: string;
  accountPath: string;
  loadedPages: Map<number, { info: PageInfo; nodes: ExplorerNode[] }>;
  pagePaths: Map<number, string>;
  expandedNodes: Set<string>;
  showEmptySlots: boolean;
  showHashes: boolean;
  onNavigate: (pageId: number, basePath?: string, isChildPage?: boolean) => void;
  onToggleNode: (pageId: number, cellIndex: number) => void;
  onExpandAllOnPage: (pageId: number) => void;
  onCollapseAllOnPage: (pageId: number) => void;
  depth: number;
}

function RemoteChildPointer({
  child,
  parentPath,
  accountPath,
  loadedPages,
  pagePaths,
  expandedNodes,
  showEmptySlots,
  showHashes,
  onNavigate,
  onToggleNode,
  onExpandAllOnPage,
  onCollapseAllOnPage,
  depth,
}: RemoteChildPointerProps) {
  const nibble = child.index.toString(16).toUpperCase();
  const childBasePath = parentPath + nibble;
  const pageId = child.pointer.pageId!;
  const pageData = loadedPages.get(pageId);

  const pageTree = useMemo(() => {
    if (!pageData) return null;
    return buildTree(pageData.nodes, childBasePath);
  }, [pageData, childBasePath]);

  if (!pageData) {
    return (
      <div className="remote-pointer-box" style={{ marginLeft: depth * 20 }}>
        <span className="slot-nibble">[{nibble}]</span>
        <span
          className="child-pointer other-page"
          onClick={() => onNavigate(pageId, childBasePath, true)}
        >
          Page {pageId} (click to load)
        </span>
        {showHashes && child.pointer.rlpHash && (
          <span className="pointer-hash" title={child.pointer.rlpHash}>
            {child.pointer.rlpHash}
          </span>
        )}
      </div>
    );
  }

  const fullnessColor = getFullnessColor(pageData.info.occupancyPercent);

  return (
    <div className="loaded-subtree" style={{ marginLeft: depth * 20 }}>
      <div className="subtree-header" style={{ backgroundColor: fullnessColor }}>
        <span className="slot-nibble">[{nibble}]</span>
        <span className="subtree-page-id">Page {pageId}</span>
        <span className="subtree-page-stats">{pageData.info.cellCount} nodes</span>
        <span className="subtree-page-stats">
          {pageData.info.usedBytes} / {pageData.info.totalBytes} bytes
        </span>
        <span className="subtree-page-stats">{pageData.info.occupancyPercent.toFixed(1)}% full</span>
        {showHashes && child.pointer.rlpHash && (
          <span className="pointer-hash" title={child.pointer.rlpHash}>
            {child.pointer.rlpHash}
          </span>
        )}
        <span className="page-actions">
          <button className="btn-small" onClick={() => onExpandAllOnPage(pageId)} title="Expand all">+</button>
          <button className="btn-small" onClick={() => onCollapseAllOnPage(pageId)} title="Collapse all">−</button>
        </span>
      </div>
      {pageTree?.map((treeNode) => (
        <TreeNodeComponent
          key={`${treeNode.node.pageId}:${treeNode.node.cellIndex}`}
          treeNode={treeNode}
          depth={depth}
          accountPath={accountPath}
          expandedNodes={expandedNodes}
          loadedPages={loadedPages}
          pagePaths={pagePaths}
          showEmptySlots={showEmptySlots}
          showHashes={showHashes}
          onToggleNode={onToggleNode}
          onNavigate={onNavigate}
          onExpandAllOnPage={onExpandAllOnPage}
          onCollapseAllOnPage={onCollapseAllOnPage}
        />
      ))}
    </div>
  );
}

interface StorageRootPointerProps {
  pageId: number;
  rlpHash?: string;
  accountPath: string;
  loadedPages: Map<number, { info: PageInfo; nodes: ExplorerNode[] }>;
  pagePaths: Map<number, string>;
  expandedNodes: Set<string>;
  showEmptySlots: boolean;
  showHashes: boolean;
  onNavigate: (pageId: number, basePath?: string, isChildPage?: boolean) => void;
  onToggleNode: (pageId: number, cellIndex: number) => void;
  onExpandAllOnPage: (pageId: number) => void;
  onCollapseAllOnPage: (pageId: number) => void;
  depth: number;
}

function StorageRootPointer({
  pageId,
  rlpHash,
  accountPath,
  loadedPages,
  pagePaths,
  expandedNodes,
  showEmptySlots,
  showHashes,
  onNavigate,
  onToggleNode,
  onExpandAllOnPage,
  onCollapseAllOnPage,
  depth,
}: StorageRootPointerProps) {
  const pageData = loadedPages.get(pageId);

  const pageTree = useMemo(() => {
    if (!pageData) return null;
    return buildTree(pageData.nodes, '');
  }, [pageData]);

  if (!pageData) {
    return (
      <div className="storage-pointer-box">
        <span className="storage-label">Storage:</span>
        <span
          className="child-pointer other-page"
          onClick={() => onNavigate(pageId, '', true)}
        >
          Page {pageId} (click to load)
        </span>
        {showHashes && rlpHash && (
          <span className="pointer-hash" title={rlpHash}>
            {rlpHash}
          </span>
        )}
      </div>
    );
  }

  const fullnessColor = getFullnessColor(pageData.info.occupancyPercent);

  return (
    <div className="loaded-storage-subtree">
      <div className="subtree-header" style={{ backgroundColor: fullnessColor }}>
        <span className="storage-label">Storage</span>
        <span className="subtree-page-id">Page {pageId}</span>
        <span className="subtree-page-stats">{pageData.info.cellCount} nodes</span>
        <span className="subtree-page-stats">
          {pageData.info.usedBytes} / {pageData.info.totalBytes} bytes
        </span>
        <span className="subtree-page-stats">{pageData.info.occupancyPercent.toFixed(1)}% full</span>
        {showHashes && rlpHash && (
          <span className="pointer-hash" title={rlpHash}>
            {rlpHash}
          </span>
        )}
        <span className="page-actions">
          <button className="btn-small" onClick={() => onExpandAllOnPage(pageId)} title="Expand all">+</button>
          <button className="btn-small" onClick={() => onCollapseAllOnPage(pageId)} title="Collapse all">−</button>
        </span>
      </div>
      {pageTree?.map((treeNode) => (
        <TreeNodeComponent
          key={`${treeNode.node.pageId}:${treeNode.node.cellIndex}`}
          treeNode={treeNode}
          depth={depth}
          accountPath={accountPath}
          expandedNodes={expandedNodes}
          loadedPages={loadedPages}
          pagePaths={pagePaths}
          showEmptySlots={showEmptySlots}
          showHashes={showHashes}
          onToggleNode={onToggleNode}
          onNavigate={onNavigate}
          onExpandAllOnPage={onExpandAllOnPage}
          onCollapseAllOnPage={onCollapseAllOnPage}
        />
      ))}
    </div>
  );
}
