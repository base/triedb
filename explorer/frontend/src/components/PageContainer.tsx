import { useMemo } from 'react';
import type { ExplorerNode, PageInfo } from '../types';
import { TreeNodeComponent } from './TreeNodeComponent';
import { buildTree } from '../utils/treeBuilder';

interface PageContainerProps {
  pageInfo: PageInfo;
  nodes: ExplorerNode[];
  basePath: string;
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

function getFullnessColor(percent: number): string {
  // HSL: 120=green, 60=yellow, 0=red
  const hue = Math.max(0, 120 - percent * 1.2);
  return `hsl(${hue}, 60%, 92%)`;
}

export function PageContainer({
  pageInfo,
  nodes,
  basePath,
  expandedNodes,
  loadedPages,
  pagePaths,
  showEmptySlots,
  showHashes,
  onToggleNode,
  onNavigate,
  onExpandAllOnPage,
  onCollapseAllOnPage,
}: PageContainerProps) {
  const bgColor = getFullnessColor(pageInfo.occupancyPercent);

  // Build tree structure from flat node list
  const treeRoots = useMemo(() => buildTree(nodes, basePath), [nodes, basePath]);

  return (
    <div className="page-container">
      <div className="page-header" style={{ backgroundColor: bgColor }}>
        <span className="page-id">Page {pageInfo.pageId}</span>
        <span className="page-stats">{pageInfo.cellCount} nodes</span>
        <span className="page-stats">
          {pageInfo.usedBytes} / {pageInfo.totalBytes} bytes
        </span>
        <span className="page-stats">{pageInfo.occupancyPercent.toFixed(1)}% full</span>
        <span className="page-actions">
          <button className="btn-small" onClick={() => onExpandAllOnPage(pageInfo.pageId)} title="Expand all nodes">+</button>
          <button className="btn-small" onClick={() => onCollapseAllOnPage(pageInfo.pageId)} title="Collapse all nodes">−</button>
        </span>
      </div>
      <div className="page-nodes">
        {treeRoots.map((treeNode) => (
          <TreeNodeComponent
            key={`${treeNode.node.pageId}:${treeNode.node.cellIndex}`}
            treeNode={treeNode}
            depth={0}
            accountPath=""
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
    </div>
  );
}
