import { useEffect, useState } from 'react';
import { useTrieData } from './hooks/useTrieData';
import { PageContainer } from './components/PageContainer';
import { SearchBar } from './components/SearchBar';
import { MetadataModal } from './components/MetadataModal';
import type { PathSearchResult } from './types';
import './styles/index.css';

export function App() {
  const {
    state,
    loadRootPage,
    loadPage,
    toggleNode,
    isPageLoaded,
    getPageBasePath,
    loadSearchPath,
    toggleAutoExpand,
    toggleShowEmptySlots,
    toggleShowHashes,
    expandAllOnPage,
    collapseAllOnPage,
  } = useTrieData();

  const [isMetadataOpen, setIsMetadataOpen] = useState(false);
  const [searchResult, setSearchResult] = useState<PathSearchResult | null>(null);

  useEffect(() => {
    loadRootPage();
  }, [loadRootPage]);

  const handleNavigate = (pageId: number, basePath?: string, isChildPage: boolean = true) => {
    if (!isPageLoaded(pageId)) {
      loadPage(pageId, basePath, isChildPage);
    }
  };

  const handleSearchResult = async (result: PathSearchResult | null) => {
    setSearchResult(result);
    if (result) {
      // Load pages along the search path with proper hierarchy
      await loadSearchPath(result);
    }
  };

  // Sort pages by ID for consistent display, filtering out child pages
  const sortedPages = Array.from(state.loadedPages.entries())
    .filter(([pageId]) => !state.childPages.has(pageId))
    .sort(([a], [b]) => a - b);

  return (
    <div className="app">
      <header className="header">
        <h1>TrieDB Explorer</h1>
        <SearchBar onSearchResult={handleSearchResult} />
        <div className="header-actions">
          <button
            className={`btn ${state.autoExpand ? 'btn-primary' : 'btn-secondary'}`}
            onClick={toggleAutoExpand}
            title="Auto-expand nodes as pages are loaded"
          >
            Auto-expand
          </button>
          <button
            className={`btn ${state.showEmptySlots ? 'btn-primary' : 'btn-secondary'}`}
            onClick={toggleShowEmptySlots}
            title="Show empty child slots in branches"
          >
            Empty slots
          </button>
          <button
            className={`btn ${state.showHashes ? 'btn-primary' : 'btn-secondary'}`}
            onClick={toggleShowHashes}
            title="Show RLP hashes alongside pointers"
          >
            Hashes
          </button>
          <button
            className="btn btn-secondary"
            onClick={() => setIsMetadataOpen(true)}
          >
            Metadata
          </button>
        </div>
      </header>

      <main className="main-content">
        {state.isLoading && <div className="loading">Loading...</div>}
        {state.error && <div className="error">{state.error}</div>}

        {searchResult && (
          <div className="search-result-banner">
            Found: {searchResult.node.nodeType} at Page {searchResult.node.pageId},
            Cell {searchResult.node.cellIndex}
          </div>
        )}

        <div className="tree-view">
          {sortedPages.map(([pageId, pageData]) => (
            <PageContainer
              key={pageId}
              pageInfo={pageData.info}
              nodes={pageData.nodes}
              basePath={getPageBasePath(pageId)}
              expandedNodes={state.expandedNodes}
              loadedPages={state.loadedPages}
              pagePaths={state.pagePaths}
              showEmptySlots={state.showEmptySlots}
              showHashes={state.showHashes}
              onToggleNode={toggleNode}
              onNavigate={handleNavigate}
              onExpandAllOnPage={expandAllOnPage}
              onCollapseAllOnPage={collapseAllOnPage}
            />
          ))}
        </div>

        {!state.isLoading && sortedPages.length === 0 && !state.error && (
          <div className="empty-message">
            No data loaded. The database may be empty.
          </div>
        )}
      </main>

      <MetadataModal
        isOpen={isMetadataOpen}
        onClose={() => setIsMetadataOpen(false)}
      />
    </div>
  );
}
