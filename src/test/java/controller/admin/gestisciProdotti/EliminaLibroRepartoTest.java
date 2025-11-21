package controller.admin.gestisciProdotti;

import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import model.libroService.RepartoDAO;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.mockito.Mockito.*;

/**
 * Test class for EliminaLibroReparto
 * Tests the functionality of removing a libro from a reparto
 */
class EliminaLibroRepartoTest {

    private EliminaLibroReparto servlet;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private RequestDispatcher dispatcher;
    private RepartoDAO repartoDAO;

    @BeforeEach
    void setUp() {
        servlet = new EliminaLibroReparto();
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        dispatcher = mock(RequestDispatcher.class);
        repartoDAO = mock(RepartoDAO.class);
    }

    /**
     * Test successful deletion of libro from reparto with valid parameters
     * Expected: deleteFromAppartenenzaLibro is called and forwards to "modifica-libro"
     */
    @Test
    void testDoGet_SuccessfulDeletion() throws Exception {
        when(request.getParameter("isbn")).thenReturn("1234567890123");
        when(request.getParameter("idReparto")).thenReturn("1");
        when(request.getRequestDispatcher("modifica-libro")).thenReturn(dispatcher);
        doNothing().when(repartoDAO).deleteFromAppartenenzaLibro(1, "1234567890123");

        servlet.setRepartoDAO(repartoDAO);
        servlet.doGet(request, response);

        verify(repartoDAO).deleteFromAppartenenzaLibro(1, "1234567890123");
        verify(request).getRequestDispatcher("modifica-libro");
        verify(dispatcher).forward(request, response);
    }

    /**
     * Test when isbn parameter is null
     * Expected: deleteFromAppartenenzaLibro is called with null isbn
     */
    @Test
    void testDoGet_IsbnNull() throws Exception {
        when(request.getParameter("isbn")).thenReturn(null);
        when(request.getParameter("idReparto")).thenReturn("1");
        when(request.getRequestDispatcher("modifica-libro")).thenReturn(dispatcher);
        doNothing().when(repartoDAO).deleteFromAppartenenzaLibro(1, null);

        servlet.setRepartoDAO(repartoDAO);
        servlet.doGet(request, response);

        verify(repartoDAO).deleteFromAppartenenzaLibro(1, null);
        verify(dispatcher).forward(request, response);
    }

    /**
     * Test when idReparto parameter is invalid (null, empty, or non-numeric)
     * Expected: NumberFormatException is thrown
     */
    @Test
    void testDoGet_IdRepartoInvalid() throws Exception {
        when(request.getParameter("isbn")).thenReturn("1234567890123");
        when(request.getParameter("idReparto")).thenReturn("abc");

        servlet.setRepartoDAO(repartoDAO);

        try {
            servlet.doGet(request, response);
        } catch (NumberFormatException e) {
            // Expected exception
        }

        verify(repartoDAO, never()).deleteFromAppartenenzaLibro(anyInt(), anyString());
        verify(dispatcher, never()).forward(request, response);
    }


    /**
     * Test when deleteFromAppartenenzaLibro throws an exception
     * Expected: exception propagates up
     */
    @Test
    void testDoGet_DeleteThrowsException() throws Exception {
        when(request.getParameter("isbn")).thenReturn("1234567890123");
        when(request.getParameter("idReparto")).thenReturn("1");
        doThrow(new RuntimeException("Database error")).when(repartoDAO).deleteFromAppartenenzaLibro(1, "1234567890123");

        servlet.setRepartoDAO(repartoDAO);

        try {
            servlet.doGet(request, response);
        } catch (RuntimeException e) {
            // Expected exception
        }

        verify(repartoDAO).deleteFromAppartenenzaLibro(1, "1234567890123");
        verify(dispatcher, never()).forward(request, response);
    }
}
