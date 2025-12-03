import type {
  ApiResponse,
  DatabaseInfo,
  DescendantsResponse,
  ExplorerNode,
  PageInfo,
  PageResponse,
  PathSearchResult,
  RootResponse,
} from '../types';

const API_BASE = '/api';

async function fetchApi<T>(url: string): Promise<ApiResponse<T>> {
  const response = await fetch(`${API_BASE}${url}`);
  return response.json();
}

export async function getRoot(): Promise<ApiResponse<RootResponse>> {
  return fetchApi('/root');
}

export async function getPage(pageId: number): Promise<ApiResponse<PageResponse>> {
  return fetchApi(`/pages/${pageId}`);
}

export async function getPageInfo(pageId: number): Promise<ApiResponse<PageInfo>> {
  return fetchApi(`/pages/${pageId}/info`);
}

export async function getDescendants(pageId: number): Promise<ApiResponse<DescendantsResponse>> {
  return fetchApi(`/pages/${pageId}/descendants`);
}

export async function getNodeDescendants(
  pageId: number,
  cellIndex: number
): Promise<ApiResponse<DescendantsResponse>> {
  return fetchApi(`/pages/${pageId}/nodes/${cellIndex}/descendants`);
}

export async function getNode(
  pageId: number,
  cellIndex: number
): Promise<ApiResponse<ExplorerNode>> {
  return fetchApi(`/nodes/${pageId}/${cellIndex}`);
}

export async function search(
  query: string,
  type: 'raw' | 'address' | 'storage' = 'raw'
): Promise<ApiResponse<PathSearchResult | null>> {
  return fetchApi(`/search?q=${encodeURIComponent(query)}&type=${type}`);
}

export async function getMetadata(): Promise<ApiResponse<DatabaseInfo>> {
  return fetchApi('/metadata');
}
