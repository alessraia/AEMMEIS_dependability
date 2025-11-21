package controller.admin.gestisciReparti;

import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import model.libroService.RepartoDAO;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.mockito.Mockito.*;

/**
 * Test class for EliminaRepartoServlet
 * Tests the functionality of deleting a department (Reparto) from the system
 */
class EliminaRepartoServletTest {

    private EliminaRepartoServlet servlet;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private RepartoDAO repartoDAO;

    @BeforeEach
    void setUp() {
        servlet = new EliminaRepartoServlet();
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        repartoDAO = mock(RepartoDAO.class);
    }

    /**
     * Test successful deletion of a reparto with valid ID
     * Expected: deleteReparto is called and redirects to "gestisci-reparti"
     */
    @Test
    void testDoGet_SuccessfulDeletion() throws Exception {
        when(request.getParameter("idReparto")).thenReturn("1");
        doNothing().when(repartoDAO).deleteReparto(1);

        servlet.setRepartoDAO(repartoDAO);
        servlet.doGet(request, response);

        verify(repartoDAO).deleteReparto(1);
        verify(response).sendRedirect("gestisci-reparti");
    }

    /**
     * Test deletion with a different valid ID
     * Expected: deleteReparto is called with correct ID and redirects
     */
    @Test
    void testDoGet_DeletionWithDifferentId() throws Exception {
        when(request.getParameter("idReparto")).thenReturn("5");
        doNothing().when(repartoDAO).deleteReparto(5);

        servlet.setRepartoDAO(repartoDAO);
        servlet.doGet(request, response);

        verify(repartoDAO).deleteReparto(5);
        verify(response).sendRedirect("gestisci-reparti");
    }

    /**
     * Test deletion with a large ID value
     * Expected: deleteReparto is called with correct ID and redirects
     */
    @Test
    void testDoGet_DeletionWithLargeId() throws Exception {
        when(request.getParameter("idReparto")).thenReturn("999999");
        doNothing().when(repartoDAO).deleteReparto(999999);

        servlet.setRepartoDAO(repartoDAO);
        servlet.doGet(request, response);

        verify(repartoDAO).deleteReparto(999999);
        verify(response).sendRedirect("gestisci-reparti");
    }

    /**
     * Test deletion with ID zero
     * Expected: deleteReparto is called with ID 0 and redirects
     */
    @Test
    void testDoGet_DeletionWithZeroId() throws Exception {
        when(request.getParameter("idReparto")).thenReturn("0");
        doNothing().when(repartoDAO).deleteReparto(0);

        servlet.setRepartoDAO(repartoDAO);
        servlet.doGet(request, response);

        verify(repartoDAO).deleteReparto(0);
        verify(response).sendRedirect("gestisci-reparti");
    }

    /**
     * Test when idReparto parameter is null
     * Expected: NumberFormatException is thrown
     */
    @Test
    void testDoGet_IdRepartoNull() throws Exception {
        when(request.getParameter("idReparto")).thenReturn(null);

        servlet.setRepartoDAO(repartoDAO);

        try {
            servlet.doGet(request, response);
        } catch (NumberFormatException e) {
            // Expected exception
        }

        verify(repartoDAO, never()).deleteReparto(anyInt());
        verify(response, never()).sendRedirect(anyString());
    }

    /**
     * Test when idReparto parameter is empty string
     * Expected: NumberFormatException is thrown
     */
    @Test
    void testDoGet_IdRepartoEmpty() throws Exception {
        when(request.getParameter("idReparto")).thenReturn("");

        servlet.setRepartoDAO(repartoDAO);

        try {
            servlet.doGet(request, response);
        } catch (NumberFormatException e) {
            // Expected exception
        }

        verify(repartoDAO, never()).deleteReparto(anyInt());
        verify(response, never()).sendRedirect(anyString());
    }

    /**
     * Test when idReparto parameter is not a valid integer
     * Expected: NumberFormatException is thrown
     */
    @Test
    void testDoGet_IdRepartoNotANumber() throws Exception {
        when(request.getParameter("idReparto")).thenReturn("abc");

        servlet.setRepartoDAO(repartoDAO);

        try {
            servlet.doGet(request, response);
        } catch (NumberFormatException e) {
            // Expected exception
        }

        verify(repartoDAO, never()).deleteReparto(anyInt());
        verify(response, never()).sendRedirect(anyString());
    }

    /**
     * Test when idReparto parameter contains special characters
     * Expected: NumberFormatException is thrown
     */
    @Test
    void testDoGet_IdRepartoWithSpecialCharacters() throws Exception {
        when(request.getParameter("idReparto")).thenReturn("1@#$");

        servlet.setRepartoDAO(repartoDAO);

        try {
            servlet.doGet(request, response);
        } catch (NumberFormatException e) {
            // Expected exception
        }

        verify(repartoDAO, never()).deleteReparto(anyInt());
        verify(response, never()).sendRedirect(anyString());
    }

    /**
     * Test when idReparto parameter is a decimal number
     * Expected: NumberFormatException is thrown
     */
    @Test
    void testDoGet_IdRepartoDecimal() throws Exception {
        when(request.getParameter("idReparto")).thenReturn("10.5");

        servlet.setRepartoDAO(repartoDAO);

        try {
            servlet.doGet(request, response);
        } catch (NumberFormatException e) {
            // Expected exception
        }

        verify(repartoDAO, never()).deleteReparto(anyInt());
        verify(response, never()).sendRedirect(anyString());
    }

    /**
     * Test when idReparto parameter has leading/trailing whitespace
     * Expected: NumberFormatException is thrown (Integer.parseInt doesn't trim)
     */
    @Test
    void testDoGet_IdRepartoWithWhitespace() throws Exception {
        when(request.getParameter("idReparto")).thenReturn("  10  ");

        servlet.setRepartoDAO(repartoDAO);

        try {
            servlet.doGet(request, response);
        } catch (NumberFormatException e) {
            // Expected exception
        }

        verify(repartoDAO, never()).deleteReparto(anyInt());
        verify(response, never()).sendRedirect(anyString());
    }

    /**
     * Test when idReparto parameter is a negative number
     * Expected: deleteReparto is called with negative ID (valid integer)
     */
    @Test
    void testDoGet_IdRepartoNegative() throws Exception {
        when(request.getParameter("idReparto")).thenReturn("-5");
        doNothing().when(repartoDAO).deleteReparto(-5);

        servlet.setRepartoDAO(repartoDAO);
        servlet.doGet(request, response);

        verify(repartoDAO).deleteReparto(-5);
        verify(response).sendRedirect("gestisci-reparti");
    }

    /**
     * Test when deleteReparto throws an exception
     * Expected: exception propagates up
     */
    @Test
    void testDoGet_DeleteRepartoThrowsException() throws Exception {
        when(request.getParameter("idReparto")).thenReturn("1");
        doThrow(new RuntimeException("Database error")).when(repartoDAO).deleteReparto(1);

        servlet.setRepartoDAO(repartoDAO);

        try {
            servlet.doGet(request, response);
        } catch (RuntimeException e) {
            // Expected exception
        }

        verify(repartoDAO).deleteReparto(1);
        verify(response, never()).sendRedirect(anyString());
    }

    /**
     * Test deletion is called exactly once
     * Expected: deleteReparto is invoked only once per request
     */
    @Test
    void testDoGet_DeleteRepartoCalledOnce() throws Exception {
        when(request.getParameter("idReparto")).thenReturn("3");
        doNothing().when(repartoDAO).deleteReparto(3);

        servlet.setRepartoDAO(repartoDAO);
        servlet.doGet(request, response);

        verify(repartoDAO, times(1)).deleteReparto(3);
        verify(response, times(1)).sendRedirect("gestisci-reparti");
    }
}
