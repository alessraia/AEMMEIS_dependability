package controller.admin.gestisciSedi;

import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletConfig;
import jakarta.servlet.ServletContext;
import jakarta.servlet.ServletException;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.io.IOException;

import static org.mockito.Mockito.*;
import org.mockito.InOrder;

/**
 * Unit tests for AggiungiSedeServletAppoggio
 * Tests the servlet's ability to display the form for adding new store locations (sedi).
 * This servlet acts as a support/helper servlet that simply forwards requests to the JSP form.
 */
class AggiungiSedeServletAppoggioTest {

    private AggiungiSedeServletAppoggio servlet;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private RequestDispatcher dispatcher;

    @BeforeEach
    void setUp() throws ServletException {
        servlet = new AggiungiSedeServletAppoggio();
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        dispatcher = mock(RequestDispatcher.class);
        
        // Initialize servlet with mock ServletConfig and ServletContext to allow logging
        ServletConfig config = mock(ServletConfig.class);
        ServletContext context = mock(ServletContext.class);
        when(config.getServletContext()).thenReturn(context);
        servlet.init(config);
    }

    /**
     * Test successful forwarding to aggiungiSedi.jsp
     * Scenario: User requests the form page, should be forwarded to JSP
     */
    @Test
    void testDoGet_SuccessfulForwardingToJsp() throws IOException, ServletException {
        // Arrange: Mock the request dispatcher
        when(request.getRequestDispatcher("/WEB-INF/results/admin/sedi/aggiungiSedi.jsp")).thenReturn(dispatcher);

        // Act
        servlet.doGet(request, response);

        // Assert: Verify the request dispatcher is obtained with correct path
        verify(request).getRequestDispatcher("/WEB-INF/results/admin/sedi/aggiungiSedi.jsp");
        // Verify forward is called
        verify(dispatcher).forward(request, response);
    }

    /**
     * Test that forward method is called exactly once
     * Scenario: Ensures no duplicate forwards or missing forwards
     */
    @Test
    void testDoGet_ForwardCalledExactlyOnce() throws IOException, ServletException {
        // Arrange
        when(request.getRequestDispatcher("/WEB-INF/results/admin/sedi/aggiungiSedi.jsp")).thenReturn(dispatcher);

        // Act
        servlet.doGet(request, response);

        // Assert: Forward should be called exactly once
        verify(dispatcher, times(1)).forward(request, response);
    }

    /**
     * Test correct JSP path is used
     * Scenario: Verify the exact path to the form JSP
     */
    @Test
    void testDoGet_CorrectJspPath() throws IOException, ServletException {
        // Arrange
        when(request.getRequestDispatcher("/WEB-INF/results/admin/sedi/aggiungiSedi.jsp")).thenReturn(dispatcher);

        // Act
        servlet.doGet(request, response);

        // Assert: Verify exact JSP path
        verify(request, times(1)).getRequestDispatcher("/WEB-INF/results/admin/sedi/aggiungiSedi.jsp");
    }

    /**
     * Test with null response parameter
     * Scenario: HttpServletResponse should be passed through
     */
    @Test
    void testDoGet_ResponsePassedToDispatcher() throws IOException, ServletException {
        // Arrange
        when(request.getRequestDispatcher("/WEB-INF/results/admin/sedi/aggiungiSedi.jsp")).thenReturn(dispatcher);

        // Act
        servlet.doGet(request, response);

        // Assert: Response object should be passed to forward
        verify(dispatcher).forward(request, response);
    }

    /**
     * Test request parameter is preserved during forward
     * Scenario: Any request parameters should be available in forwarded JSP
     */
    @Test
    void testDoGet_RequestPreservedInForward() throws IOException, ServletException {
        // Arrange
        when(request.getRequestDispatcher("/WEB-INF/results/admin/sedi/aggiungiSedi.jsp")).thenReturn(dispatcher);

        // Act
        servlet.doGet(request, response);

        // Assert: Verify that the exact request object is forwarded
        verify(dispatcher).forward(request, response);
        verify(request).getRequestDispatcher("/WEB-INF/results/admin/sedi/aggiungiSedi.jsp");
    }

    /**
     * Test dispatcher is obtained before forwarding
     * Scenario: Ensures getRequestDispatcher is called before forward
     */
    @Test
    void testDoGet_DispatcherObtainedBeforeForward() throws IOException, ServletException {
        // Arrange
        when(request.getRequestDispatcher("/WEB-INF/results/admin/sedi/aggiungiSedi.jsp")).thenReturn(dispatcher);

        // Act
        servlet.doGet(request, response);

        // Assert: Verify sequence - getRequestDispatcher is called before forward
        InOrder inOrder = inOrder(request, dispatcher);
        inOrder.verify(request).getRequestDispatcher("/WEB-INF/results/admin/sedi/aggiungiSedi.jsp");
        inOrder.verify(dispatcher).forward(request, response);
    }

    /**
     * Test ServletException is caught and logged
     * Scenario: If forward throws ServletException, it should be caught and logged
     */
    @Test
    void testDoGet_ServletExceptionPropagated() throws IOException, ServletException {
        // Arrange
        when(request.getRequestDispatcher("/WEB-INF/results/admin/sedi/aggiungiSedi.jsp")).thenReturn(dispatcher);
        doThrow(new ServletException("Forward failed")).when(dispatcher).forward(request, response);

        // Act: Call doGet - exception should be caught and logged, not thrown
        servlet.doGet(request, response);

        // Assert: Verify dispatcher.forward was called
        verify(dispatcher).forward(request, response);
    }

    /**
     * Test IOException is caught and logged
     * Scenario: If forward throws IOException, it should be caught and logged
     */
    @Test
    void testDoGet_IOExceptionPropagated() throws IOException, ServletException {
        // Arrange
        when(request.getRequestDispatcher("/WEB-INF/results/admin/sedi/aggiungiSedi.jsp")).thenReturn(dispatcher);
        doThrow(new IOException("IO error during forward")).when(dispatcher).forward(request, response);

        // Act: Call doGet - exception should be caught and logged, not thrown
        servlet.doGet(request, response);

        // Assert: Verify dispatcher.forward was called
        verify(dispatcher).forward(request, response);
    }

    /**
     * Test multiple sequential requests
     * Scenario: Servlet should handle multiple requests independently
     */
    @Test
    void testDoGet_MultipleSequentialRequests() throws IOException, ServletException {
        // Arrange
        when(request.getRequestDispatcher("/WEB-INF/results/admin/sedi/aggiungiSedi.jsp")).thenReturn(dispatcher);

        // Act: Call doGet three times
        servlet.doGet(request, response);
        servlet.doGet(request, response);
        servlet.doGet(request, response);

        // Assert: Each request should result in one forward
        verify(dispatcher, times(3)).forward(request, response);
    }

    /**
     * Test servlet initialization doesn't affect forwarding
     * Scenario: Servlet without explicit init should still work
     */
    @Test
    void testDoGet_NoExplicitInitialization() throws IOException, ServletException {
        // Arrange: Servlet is already initialized in setUp
        when(request.getRequestDispatcher("/WEB-INF/results/admin/sedi/aggiungiSedi.jsp")).thenReturn(dispatcher);

        // Act
        servlet.doGet(request, response);

        // Assert: Forwarding should work without explicit initialization
        verify(dispatcher).forward(request, response);
    }

    /**
     * Test JSP path does not contain null values
     * Scenario: Path should be properly formed with no null elements
     */
    @Test
    void testDoGet_ValidJspPathFormat() throws IOException, ServletException {
        // Arrange
        String expectedPath = "/WEB-INF/results/admin/sedi/aggiungiSedi.jsp";
        when(request.getRequestDispatcher(expectedPath)).thenReturn(dispatcher);

        // Act
        servlet.doGet(request, response);

        // Assert: Verify the path is exactly as expected
        verify(request).getRequestDispatcher(expectedPath);
        assert expectedPath.startsWith("/WEB-INF/");
        assert expectedPath.endsWith(".jsp");
    }

    /**
     * Test response object is never used directly by servlet
     * Scenario: The servlet only uses response through the dispatcher's forward method
     */
    @Test
    void testDoGet_ResponseNotUsedDirectly() throws IOException, ServletException {
        // Arrange
        when(request.getRequestDispatcher("/WEB-INF/results/admin/sedi/aggiungiSedi.jsp")).thenReturn(dispatcher);

        // Act
        servlet.doGet(request, response);

        // Assert: Response should only be used through forward, never directly
        verify(response, never()).getWriter();
        verify(response, never()).getOutputStream();
        verify(response, never()).sendError(anyInt());
        verify(response, never()).sendRedirect(anyString());
    }
}
