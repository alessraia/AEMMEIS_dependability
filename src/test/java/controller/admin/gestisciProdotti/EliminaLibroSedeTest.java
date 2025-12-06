package controller.admin.gestisciProdotti;

import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletConfig;
import jakarta.servlet.ServletContext;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import model.libroService.SedeDAO;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.mockito.Mockito.*;

/**
 * Test class for EliminaLibroSede
 * Tests the functionality of removing a libro from a sede
 */
class EliminaLibroSedeTest {

    private EliminaLibroSede servlet;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private RequestDispatcher dispatcher;
    private SedeDAO sedeDAO;

    @BeforeEach
    void setUp() throws Exception {
        servlet = new EliminaLibroSede();
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        dispatcher = mock(RequestDispatcher.class);
        sedeDAO = mock(SedeDAO.class);
        
        // Initialize servlet with ServletConfig
        ServletConfig servletConfig = mock(ServletConfig.class);
        ServletContext servletContext = mock(ServletContext.class);
        when(servletConfig.getServletContext()).thenReturn(servletContext);
        servlet.init(servletConfig);
    }

    /**
     * Test successful deletion of libro from sede with valid parameters
     * Expected: deleteFromPresenzaLibro is called and forwards to "modifica-libro"
     */
    @Test
    void testDoGet_SuccessfulDeletion() throws Exception {
        when(request.getParameter("isbn")).thenReturn("1234567890123");
        when(request.getParameter("idSede")).thenReturn("1");
        when(request.getRequestDispatcher("modifica-libro")).thenReturn(dispatcher);
        doNothing().when(sedeDAO).deleteFromPresenzaLibro(1, "1234567890123");

        servlet.setSedeDAO(sedeDAO);
        servlet.doGet(request, response);

        verify(sedeDAO).deleteFromPresenzaLibro(1, "1234567890123");
        verify(request).getRequestDispatcher("modifica-libro");
        verify(dispatcher).forward(request, response);
    }

    /**
     * Test when isbn parameter is null
     * Expected: deleteFromPresenzaLibro is called with null isbn
     */
    @Test
    void testDoGet_IsbnNull() throws Exception {
        when(request.getParameter("isbn")).thenReturn(null);
        when(request.getParameter("idSede")).thenReturn("1");
        when(request.getRequestDispatcher("modifica-libro")).thenReturn(dispatcher);
        doNothing().when(sedeDAO).deleteFromPresenzaLibro(1, null);

        servlet.setSedeDAO(sedeDAO);
        servlet.doGet(request, response);

        verify(sedeDAO).deleteFromPresenzaLibro(1, null);
        verify(dispatcher).forward(request, response);
    }

    /**
     * Test when idSede parameter is invalid (null, empty, or non-numeric)
     * Expected: NumberFormatException is caught and forwards to error page
     */
    @Test
    void testDoGet_IdSedeInvalid() throws Exception {
        when(request.getParameter("isbn")).thenReturn("1234567890123");
        when(request.getParameter("idSede")).thenReturn("abc");
        RequestDispatcher errorDispatcher = mock(RequestDispatcher.class);
        when(request.getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp")).thenReturn(errorDispatcher);

        servlet.setSedeDAO(sedeDAO);
        servlet.doGet(request, response);

        verify(sedeDAO, never()).deleteFromPresenzaLibro(anyInt(), anyString());
        verify(errorDispatcher).forward(request, response);
    }


    /**
     * Test when deleteFromPresenzaLibro throws an exception
     * Expected: exception propagates up
     */
    @Test
    void testDoGet_DeleteThrowsException() throws Exception {
        when(request.getParameter("isbn")).thenReturn("1234567890123");
        when(request.getParameter("idSede")).thenReturn("1");
        doThrow(new RuntimeException("Database error")).when(sedeDAO).deleteFromPresenzaLibro(1, "1234567890123");

        servlet.setSedeDAO(sedeDAO);

        try {
            servlet.doGet(request, response);
        } catch (RuntimeException e) {
            // Expected exception
        }

        verify(sedeDAO).deleteFromPresenzaLibro(1, "1234567890123");
        verify(dispatcher, never()).forward(request, response);
    }
}
